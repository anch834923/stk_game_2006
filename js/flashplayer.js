/*
 * flashplayer.js - plays the site's Flash movies natively in HTML5 canvas.
 *
 * Replaces Ruffle. Movies are pre-converted from SWF by tools/swf2json into
 * "<movie>.swf.json" (shapes, bitmaps, fonts, timelines, sounds, AVM1 bytecode);
 * this file implements the subset of Flash Player 6 needed to play them:
 * timelines and display list, shapes/morph shapes/bitmaps/text, colour
 * transforms, masks, buttons, an AVM1 bytecode interpreter, and event sounds.
 *
 * Each <embed type="application/x-shockwave-flash"> (or a bare <object> with a
 * "movie" param) is swapped for a same-sized element hosting a canvas, matching
 * the box Ruffle produced so the page layout is unchanged.
 */
(function () {
  "use strict";

  // -------------------------------------------------------------------------
  // Utilities

  var config = window.FlashPlayerConfig || {};
  var IDENTITY = [1, 0, 0, 1, 0, 0];
  var NO_CX = null; // identity colour transform

  function mmul(a, b) { // a * b  (apply b first, then a)
    return [
      a[0] * b[0] + a[2] * b[1], a[1] * b[0] + a[3] * b[1],
      a[0] * b[2] + a[2] * b[3], a[1] * b[2] + a[3] * b[3],
      a[0] * b[4] + a[2] * b[5] + a[4], a[1] * b[4] + a[3] * b[5] + a[5]
    ];
  }
  function minv(m) {
    var det = m[0] * m[3] - m[1] * m[2];
    if (!det) return null;
    return [m[3] / det, -m[1] / det, -m[2] / det, m[0] / det,
      (m[2] * m[5] - m[3] * m[4]) / det, (m[1] * m[4] - m[0] * m[5]) / det];
  }
  function mapPoint(m, x, y) { return [m[0] * x + m[2] * y + m[4], m[1] * x + m[3] * y + m[5]]; }
  function cxConcat(parent, child) { // child first, then parent
    if (!child) return parent;
    if (!parent) return child;
    return [
      child[0] * parent[0] / 256, child[1] * parent[1] / 256, child[2] * parent[2] / 256, child[3] * parent[3] / 256,
      child[4] * parent[0] / 256 + parent[4], child[5] * parent[1] / 256 + parent[5],
      child[6] * parent[2] / 256 + parent[6], child[7] * parent[3] / 256 + parent[7]
    ];
  }
  function clamp255(v) { return v < 0 ? 0 : v > 255 ? 255 : v; }
  function applyCx(cx, c) {
    if (!cx) return c;
    return [
      clamp255(c[0] * cx[0] / 256 + cx[4]), clamp255(c[1] * cx[1] / 256 + cx[5]),
      clamp255(c[2] * cx[2] / 256 + cx[6]), clamp255(c[3] * cx[3] / 256 + cx[7])
    ];
  }
  function cssColor(c) {
    return "rgba(" + Math.round(c[0]) + "," + Math.round(c[1]) + "," + Math.round(c[2]) + "," + (c[3] / 255) + ")";
  }
  function lerp(a, b, t) { return a + (b - a) * t; }
  function lerpArr(a, b, t) { var o = new Array(a.length); for (var i = 0; i < a.length; i++) o[i] = a[i] + (b[i] - a[i]) * t; return o; }
  function b64bytes(s) {
    var bin = atob(s), u = new Uint8Array(bin.length);
    for (var i = 0; i < bin.length; i++) u[i] = bin.charCodeAt(i);
    return u;
  }
  function loadImage(uri) {
    return new Promise(function (res, rej) {
      var img = new Image();
      img.onload = function () { res(img); };
      img.onerror = rej;
      img.src = uri;
    });
  }
  function makePath(cmds, path) {
    var p = path || new Path2D();
    for (var i = 0; i < cmds.length;) {
      var op = cmds[i];
      if (op === 0) { p.moveTo(cmds[i + 1], cmds[i + 2]); i += 3; }
      else if (op === 1) { p.lineTo(cmds[i + 1], cmds[i + 2]); i += 3; }
      else { p.quadraticCurveTo(cmds[i + 1], cmds[i + 2], cmds[i + 3], cmds[i + 4]); i += 5; }
    }
    return p;
  }
  function lerpCmds(a, b, t) {
    var o = new Array(a.length);
    for (var i = 0; i < a.length;) {
      var op = a[i], n = op === 2 ? 4 : 2;
      o[i] = op;
      for (var k = 1; k <= n; k++) o[i + k] = a[i + k] + (b[i + k] - a[i + k]) * t;
      i += n + 1;
    }
    return o;
  }
  function cmdsBounds(cmds, b) {
    for (var i = 0; i < cmds.length;) {
      var n = cmds[i] === 2 ? 4 : 2;
      for (var k = 1; k <= n; k += 2) {
        var x = cmds[i + k], y = cmds[i + k + 1];
        if (x < b[0]) b[0] = x; if (y < b[1]) b[1] = y; if (x > b[2]) b[2] = x; if (y > b[3]) b[3] = y;
      }
      i += n + 1;
    }
    return b;
  }

  // -------------------------------------------------------------------------
  // Sound

  var audio = {
    ctx: null,
    get: function () {
      if (!this.ctx) {
        var AC = window.AudioContext || window.webkitAudioContext;
        if (!AC) return null;
        this.ctx = new AC();
        var self = this;
        // Browsers start audio suspended until a user gesture.
        var resume = function () {
          if (self.ctx.state === "suspended") self.ctx.resume();
          if (self.ctx.state === "running") {
            ["pointerdown", "keydown", "touchend", "click"].forEach(function (e) { document.removeEventListener(e, resume, true); });
          }
        };
        ["pointerdown", "keydown", "touchend", "click"].forEach(function (e) { document.addEventListener(e, resume, true); });
      }
      return this.ctx;
    }
  };

  var ADPCM_INDEX = [[-1, 2], [-1, -1, 2, 4], [-1, -1, -1, -1, 2, 4, 6, 8], [-1, -1, -1, -1, -1, -1, -1, -1, 1, 2, 4, 6, 8, 10, 13, 16]];
  var ADPCM_STEP = [7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 19, 21, 23, 25, 28, 31, 34, 37, 41, 45, 50, 55, 60, 66, 73, 80, 88, 97, 107,
    118, 130, 143, 157, 173, 190, 209, 230, 253, 279, 307, 337, 371, 408, 449, 494, 544, 598, 658, 724, 796, 876, 963, 1060, 1166,
    1282, 1411, 1552, 1707, 1878, 2066, 2272, 2499, 2749, 3024, 3327, 3660, 4026, 4428, 4871, 5358, 5894, 6484, 7132, 7845, 8630,
    9493, 10442, 11487, 12635, 13899, 15289, 16818, 18500, 20350, 22385, 24623, 27086, 29794, 32767];

  // SWF ADPCM -> Float32 channel arrays.
  function decodeAdpcm(data, channels, sampleCount) {
    var pos = 0, total = data.length * 8;
    function bits(n) { var v = 0; for (var i = 0; i < n; i++, pos++) v = (v << 1) | ((data[pos >> 3] >> (7 - (pos & 7))) & 1); return v; }
    function sbits(n) { var v = bits(n); return v & (1 << (n - 1)) ? v - (1 << n) : v; }
    var nbits = bits(2) + 2, table = ADPCM_INDEX[nbits - 2], signMask = 1 << (nbits - 1);
    var out = [new Float32Array(sampleCount), new Float32Array(channels === 2 ? sampleCount : 0)];
    var written = 0, sample = [0, 0], index = [0, 0], c;
    while (written < sampleCount && pos + 22 * channels <= total) {
      for (c = 0; c < channels; c++) { sample[c] = sbits(16); index[c] = bits(6); out[c][written] = sample[c] / 32768; }
      written++;
      for (var i = 1; i < 4096 && written < sampleCount; i++) {
        if (pos + nbits * channels > total) break;
        for (c = 0; c < channels; c++) {
          var code = bits(nbits), step = ADPCM_STEP[index[c]], diff = step >> (nbits - 1);
          for (var k = 1, m = signMask >> 1; m; k++, m >>= 1) if (code & m) diff += step >> (k - 1);
          sample[c] += code & signMask ? -diff : diff;
          if (sample[c] > 32767) sample[c] = 32767; else if (sample[c] < -32768) sample[c] = -32768;
          index[c] += table[code & ~signMask];
          if (index[c] < 0) index[c] = 0; else if (index[c] > 88) index[c] = 88;
          out[c][written] = sample[c] / 32768;
        }
        written++;
      }
    }
    return out;
  }

  function decodeSound(def) {
    if (def._buffer) return def._buffer;
    var ctx = audio.get();
    if (!ctx) return (def._buffer = Promise.resolve(null));
    if (def.adpcm) {
      var ch = def.stereo ? 2 : 1;
      var pcm = decodeAdpcm(b64bytes(def.adpcm), ch, def.samples);
      var buf = ctx.createBuffer(ch, def.samples, def.rate);
      for (var c = 0; c < ch; c++) buf.getChannelData(c).set(pcm[c]);
      return (def._buffer = Promise.resolve(buf));
    }
    var bytes = b64bytes(def.uri.slice(def.uri.indexOf(",") + 1));
    def._buffer = new Promise(function (res) {
      ctx.decodeAudioData(bytes.buffer, function (b) {
        // MP3 encoder delay: Flash skips SeekSamples at the start.
        res(b);
      }, function () { res(null); });
    });
    return def._buffer;
  }

  // -------------------------------------------------------------------------
  // Movie resources

  function Movie(data, url) {
    this.data = data;
    this.url = url;
    this.chars = data.chars;
    this.images = {};
    this.paths = {}; // shape id -> compiled layers
  }
  Movie.prototype.load = function () {
    var self = this, jobs = [];
    Object.keys(this.data.bitmaps).forEach(function (id) {
      var b = self.data.bitmaps[id];
      if (!b.uri) return;
      jobs.push(Promise.all([loadImage(b.uri), b.alpha ? loadImage(b.alpha) : null]).then(function (r) {
        self.images[id] = r[1] ? mergeAlpha(r[0], r[1]) : r[0];
      }));
    });
    return Promise.all(jobs).then(function () { return self; });
  };
  // DefineBitsJPEG3: premultiplied JPEG colour + separate alpha plane.
  function mergeAlpha(img, mask) {
    var w = img.width, h = img.height;
    var c = document.createElement("canvas");
    c.width = w; c.height = h;
    var g = c.getContext("2d");
    g.drawImage(mask, 0, 0);
    var a = g.getImageData(0, 0, w, h).data;
    g.clearRect(0, 0, w, h);
    g.drawImage(img, 0, 0);
    var id = g.getImageData(0, 0, w, h), p = id.data;
    for (var i = 0; i < p.length; i += 4) {
      var al = a[i + 3];
      for (var k = 0; k < 3; k++) {
        var v = Math.min(p[i + k], al);
        p[i + k] = al ? Math.min(255, Math.round(v * 255 / al)) : 0;
      }
      p[i + 3] = al;
    }
    g.putImageData(id, 0, 0);
    return c;
  }
  Movie.prototype.shapeLayers = function (id) {
    var c = this.paths[id];
    if (c) return c;
    var def = this.chars[id];
    c = def.g.map(function (l) { return { k: l.k, s: l.s, path: makePath(l.p) }; });
    return (this.paths[id] = c);
  };
  Movie.prototype.morphLayers = function (id, ratio) {
    var def = this.chars[id], cache = this.paths[id] || (this.paths[id] = {});
    if (cache[ratio]) return cache[ratio];
    var t = ratio / 65535;
    var layers = def.g.map(function (l) {
      return { k: l.k, s: morphStyle(l.k === "f" ? l.s : l.s, t, l.k), path: makePath(t ? lerpCmds(l.p, l.p2, t) : l.p) };
    });
    // cache a bounded number of ratios
    var keys = Object.keys(cache);
    if (keys.length > 64) delete cache[keys[0]];
    return (cache[ratio] = layers);
  };
  function morphFill(s, t) {
    if (s.t === "s") return s.c2 ? { t: "s", c: lerpArr(s.c, s.c2, t) } : s;
    if (s.t === "bm") return s.m2 ? { t: "bm", id: s.id, m: lerpArr(s.m, s.m2, t), rep: s.rep, sm: s.sm } : s;
    var o = { t: s.t, spread: s.spread, m: s.m2 ? lerpArr(s.m, s.m2, t) : s.m, st: s.st2 ? s.st.map(function (x, i) { return lerpArr(x, s.st2[i], t); }) : s.st };
    if (s.focal !== undefined) o.focal = s.focal2 !== undefined ? lerp(s.focal, s.focal2, t) : s.focal;
    return o;
  }
  function morphStyle(s, t, kind) {
    if (kind === "f") return morphFill(s, t);
    var o = {}; for (var k in s) o[k] = s[k];
    if (s.w2 !== undefined) o.w = lerp(s.w, s.w2, t);
    o.f = morphFill(s.f, t);
    return o;
  }

  // -------------------------------------------------------------------------
  // Display objects

  var instanceCounter = 0;

  function DisplayObject(player, def, id) {
    this.player = player;
    this.def = def;
    this.id = id;
    this.matrix = IDENTITY;
    this.cx = NO_CX;
    this.ratio = 0;
    this.name = "";
    this.clipDepth = 0;
    this.parent = null;
    this.depth = 0;
    this.visible = true;
    this.scripted = false; // transformed by ActionScript: timeline no longer moves it
    this.placeId = 0; // identity of the PlaceObject that created it
    this.order = ++instanceCounter;
    this.removed = false;
  }
  DisplayObject.prototype.isClip = false;
  DisplayObject.prototype.localBounds = function () { return null; };
  DisplayObject.prototype.worldMatrix = function () {
    var m = this.matrix, p = this.parent;
    while (p) { m = mmul(p.matrix, m); p = p.parent; }
    return m;
  };
  DisplayObject.prototype.boundsIn = function (m) { // AABB of this object under matrix m (applied after own matrix)
    var b = this.localBounds();
    if (!b) return null;
    var mm = mmul(m, this.matrix);
    var pts = [mapPoint(mm, b[0], b[1]), mapPoint(mm, b[2], b[1]), mapPoint(mm, b[0], b[3]), mapPoint(mm, b[2], b[3])];
    var o = [Infinity, Infinity, -Infinity, -Infinity];
    pts.forEach(function (p) { o[0] = Math.min(o[0], p[0]); o[1] = Math.min(o[1], p[1]); o[2] = Math.max(o[2], p[0]); o[3] = Math.max(o[3], p[1]); });
    return o;
  };
  DisplayObject.prototype.targetPath = function () {
    if (!this.parent) return "_level0";
    return this.parent.targetPath() + "." + this.name;
  };

  // Shapes, morph shapes and static text are leaves.
  function Leaf(player, def, id) { DisplayObject.call(this, player, def, id); }
  Leaf.prototype = Object.create(DisplayObject.prototype);
  Leaf.prototype.localBounds = function () {
    var d = this.def;
    if (d.t === "m") { var t = this.ratio / 65535; return lerpArr(d.b, d.b2, t); }
    return d.b;
  };

  // Dynamic text field
  function EditText(player, def, id) {
    DisplayObject.call(this, player, def, id);
    this.text = def.text || "";
  }
  EditText.prototype = Object.create(DisplayObject.prototype);
  EditText.prototype.localBounds = function () { return this.def.b; };

  // Button (DefineButton)
  function Button(player, def, id) {
    DisplayObject.call(this, player, def, id);
    this.state = 1; // 1 up, 2 over, 4 down
    this.children = {};
    this.hitChildren = [];
    this.buildState();
  }
  Button.prototype = Object.create(DisplayObject.prototype);
  Button.prototype.buildState = function () {
    var self = this, kids = {};
    this.def.rec.forEach(function (r) {
      if (!(r.st & self.state)) return;
      var o = self.player.instantiate(r.c);
      if (!o) return;
      o.matrix = r.m; o.cx = r.cx; o.depth = r.d; o.parent = self;
      kids[r.d] = o;
    });
    this.children = kids;
    this.childList = Object.keys(kids).map(Number).sort(function (a, b) { return a - b; }).map(function (d) { return kids[d]; });
    this.hitChildren = this.def.rec.filter(function (r) { return r.st & 8; }).map(function (r) {
      var o = self.player.instantiate(r.c);
      o.matrix = r.m; o.parent = self;
      return o;
    });
  };
  Button.prototype.setState = function (s) {
    if (s === this.state) return;
    this.state = s;
    this.buildState();
  };
  Button.prototype.localBounds = function () {
    var b = null;
    this.childList.forEach(function (c) {
      var cb = c.boundsIn(IDENTITY);
      if (cb) b = b ? [Math.min(b[0], cb[0]), Math.min(b[1], cb[1]), Math.max(b[2], cb[2]), Math.max(b[3], cb[3])] : cb;
    });
    return b;
  };

  // MovieClip (sprites and the root)
  function MovieClip(player, def, id) {
    DisplayObject.call(this, player, def, id);
    this.frames = def.tl;
    this.totalFrames = def.fc || def.tl.length || 1;
    this.currentFrame = 0; // 1-based once entered
    this.playing = true;
    this.children = {}; // depth -> DisplayObject
    this.vars = Object.create(null);
    this.labels = {};
    for (var i = 0; i < this.frames.length; i++) if (this.frames[i].l) this.labels[this.frames[i].l.toLowerCase()] = i + 1;
    this.sound = null;
  }
  MovieClip.prototype = Object.create(DisplayObject.prototype);
  MovieClip.prototype.isClip = true;
  MovieClip.prototype.sortedChildren = function () {
    var c = this.children;
    return Object.keys(c).map(Number).sort(function (a, b) { return a - b; }).map(function (d) { return c[d]; });
  };
  MovieClip.prototype.localBounds = function () {
    var b = null;
    this.sortedChildren().forEach(function (c) {
      if (c.clipDepth) return;
      var cb = c.boundsIn(IDENTITY);
      if (cb) b = b ? [Math.min(b[0], cb[0]), Math.min(b[1], cb[1]), Math.max(b[2], cb[2]), Math.max(b[3], cb[3])] : cb;
    });
    return b;
  };
  MovieClip.prototype.childByName = function (name) {
    var lname = String(name).toLowerCase(), best = null;
    for (var d in this.children) {
      var c = this.children[d];
      if (c.name && c.name.toLowerCase() === lname && (!best || c.depth < best.depth)) best = c;
    }
    return best;
  };

  // Apply one PlaceObject/RemoveObject op from the timeline.
  MovieClip.prototype.applyOp = function (op, frameIdx, opIdx) {
    var player = this.player;
    if (op.x !== undefined) { this.removeChild(op.x); return; }
    if (op.snd !== undefined) { player.startSound(this, op.snd, op.info); return; }
    var existing = this.children[op.p];
    if (!op.mv) {
      if (existing) this.removeChild(op.p);
      var o = player.instantiate(op.c);
      if (!o) return;
      o.depth = op.p;
      o.parent = this;
      o.placeId = frameIdx * 1000 + opIdx + 1;
      if (op.m) o.matrix = op.m;
      if (op.cx) o.cx = op.cx;
      if (op.r !== undefined) o.ratio = op.r;
      if (op.n !== undefined) o.name = op.n;
      if (op.clip !== undefined) o.clipDepth = op.clip;
      this.children[op.p] = o;
      if (o.isClip) player.newClips.push(o);
      if (o.def.t === "e") player.bindText(o);
    } else if (existing) {
      if (op.c !== undefined && op.c !== existing.id) {
        // Character replacement keeps the instance's placement properties.
        var n = player.instantiate(op.c);
        if (n) {
          n.depth = existing.depth; n.parent = this; n.placeId = existing.placeId;
          n.matrix = existing.matrix; n.cx = existing.cx; n.ratio = existing.ratio;
          n.name = existing.name; n.clipDepth = existing.clipDepth; n.scripted = existing.scripted;
          existing.removed = true;
          this.children[op.p] = n;
          if (n.isClip) player.newClips.push(n);
          existing = n;
        }
      }
      if (!existing.scripted) {
        if (op.m) existing.matrix = op.m;
        if (op.cx) existing.cx = op.cx;
      }
      if (op.r !== undefined) existing.ratio = op.r;
      if (op.n !== undefined) existing.name = op.n;
      if (op.clip !== undefined) existing.clipDepth = op.clip;
    }
  };
  MovieClip.prototype.removeChild = function (depth) {
    var c = this.children[depth];
    if (!c) return;
    c.removed = true;
    if (c.isClip) c.stopSounds();
    delete this.children[depth];
  };
  MovieClip.prototype.stopSounds = function () { };

  // Enter frame n (1-based) by applying its ops; queue its actions.
  MovieClip.prototype.enterFrame = function (n) {
    this.currentFrame = n;
    var f = this.frames[n - 1];
    if (!f) return;
    if (f.o) for (var i = 0; i < f.o.length; i++) this.applyOp(f.o[i], n - 1, i);
    if (f.a) for (var j = 0; j < f.a.length; j++) this.player.queueAction(this, f.a[j]);
  };

  // gotoFrame: rebuild the display list state for frame n, keeping instances
  // that were created by the same PlaceObject (so nested clips keep playing).
  MovieClip.prototype.gotoFrame = function (n, stop) {
    if (n < 1) n = 1;
    if (n > this.totalFrames) n = this.totalFrames;
    if (stop) this.playing = false; else this.playing = true;
    if (n === this.currentFrame) return;
    if (n === this.currentFrame + 1) { this.enterFrame(n); return; }
    var state = {}; // depth -> {op merged, placeId}
    var sounds = n > this.currentFrame;
    for (var fi = 0; fi < n; fi++) {
      var f = this.frames[fi];
      if (!f || !f.o) continue;
      for (var i = 0; i < f.o.length; i++) {
        var op = f.o[i];
        if (op.snd !== undefined) continue;
        if (op.x !== undefined) { delete state[op.x]; continue; }
        if (!op.mv) state[op.p] = { c: op.c, m: op.m, cx: op.cx, r: op.r, n: op.n, clip: op.clip, placeId: fi * 1000 + i + 1 };
        else if (state[op.p]) {
          var s = state[op.p];
          if (op.c !== undefined) s.c = op.c;
          if (op.m) s.m = op.m;
          if (op.cx) s.cx = op.cx;
          if (op.r !== undefined) s.r = op.r;
          if (op.n !== undefined) s.n = op.n;
          if (op.clip !== undefined) s.clip = op.clip;
        }
      }
    }
    var self = this;
    // Remove timeline objects not present in the target state.
    Object.keys(this.children).forEach(function (d) {
      var c = self.children[d], s = state[d];
      if (!c.placeId) return; // created by script: untouched
      if (!s || s.placeId !== c.placeId) self.removeChild(+d);
    });
    Object.keys(state).forEach(function (d) {
      var s = state[d], c = self.children[d];
      if (c && c.placeId === s.placeId) {
        if (s.c !== undefined && s.c !== c.id) {
          self.applyOp({ p: +d, mv: 1, c: s.c }, 0, 0);
          c = self.children[d];
        }
        if (!c.scripted) { if (s.m) c.matrix = s.m; c.cx = s.cx || NO_CX; }
        if (s.r !== undefined) c.ratio = s.r;
        return;
      }
      if (c) return; // occupied by a script-created object
      var fi = Math.floor((s.placeId - 1) / 1000), oi = (s.placeId - 1) % 1000;
      self.applyOp({ p: +d, c: s.c, m: s.m, cx: s.cx, r: s.r, n: s.n, clip: s.clip }, fi, oi);
    });
    this.currentFrame = n;
    var tf = this.frames[n - 1];
    if (tf && tf.a) for (var j = 0; j < tf.a.length; j++) this.player.queueAction(this, tf.a[j]);
    if (sounds && tf && tf.o) for (var k = 0; k < tf.o.length; k++) if (tf.o[k].snd !== undefined) this.applyOp(tf.o[k], n - 1, k);
  };

  // Advance one frame (called once per tick when playing).
  MovieClip.prototype.step = function () {
    if (!this.playing) return;
    if (this.totalFrames <= 1) return;
    if (this.currentFrame >= this.totalFrames) this.gotoFrame(1, false);
    else this.enterFrame(this.currentFrame + 1);
  };

  // -------------------------------------------------------------------------
  // Player

  function Player(host, movie, opts) {
    this.host = host;
    this.movie = movie;
    this.opts = opts;
    this.actionQueue = [];
    this.newClips = [];
    this.textBindings = [];
    this.mouseX = 0; this.mouseY = 0; // stage twips, last known position
    this.mouseDown = false;
    this.hover = null;
    this.pressed = null;
    this.volume = 100;
    this.activeSounds = [];
    this.globals = Object.create(null);
    var d = movie.data;
    this.stageW = (d.frame[2] - d.frame[0]) / 20;
    this.stageH = (d.frame[3] - d.frame[1]) / 20;
    this.root = new MovieClip(this, { t: "sp", tl: d.tl, fc: d.fc }, 0);
    this.root.name = "";
    this.setupCanvas();
  }

  Player.prototype.setupCanvas = function () {
    var canvas = document.createElement("canvas");
    canvas.style.display = "block";
    canvas.style.width = "100%";
    canvas.style.height = "100%";
    this.host.appendChild(canvas);
    this.canvas = canvas;
    this.ctx = canvas.getContext("2d");
    this.resize();
    var self = this;
    if (window.ResizeObserver) new ResizeObserver(function () { self.resize(); self.render(); }).observe(this.host);
    window.addEventListener("resize", function () { self.resize(); self.render(); });
    this.bindMouse();
  };
  Player.prototype.resize = function () {
    var r = this.host.getBoundingClientRect();
    var dpr = window.devicePixelRatio || 1;
    // Backing store is truncated to whole device pixels (as Ruffle does).
    var w = Math.max(1, Math.floor(r.width * dpr)), h = Math.max(1, Math.floor(r.height * dpr));
    if (this.canvas.width !== w || this.canvas.height !== h) { this.canvas.width = w; this.canvas.height = h; }
    // scaleMode "showAll", centred; computed in device pixels.
    var s = Math.min(w / this.stageW, h / this.stageH);
    this.devScale = s;
    this.devX = (w - this.stageW * s) / 2;
    this.devY = (h - this.stageH * s) / 2;
    this.dpr = dpr;
    this.cssScaleX = w / r.width;
    this.cssScaleY = h / r.height;
  };
  Player.prototype.baseMatrix = function () {
    var k = this.devScale / 20;
    var d = this.movie.data.frame;
    return [k, 0, 0, k, this.devX - d[0] * k, this.devY - d[1] * k];
  };

  Player.prototype.instantiate = function (id) {
    var def = this.movie.chars[id];
    if (!def) return null;
    switch (def.t) {
      case "sp": return new MovieClip(this, def, id);
      case "b": return new Button(this, def, id);
      case "e": return new EditText(this, def, id);
      case "s": case "m": case "t": return new Leaf(this, def, id);
    }
    return null;
  };

  Player.prototype.queueAction = function (clip, code) { this.actionQueue.push([clip, code]); };
  Player.prototype.runActions = function () {
    var guard = 0;
    while (this.actionQueue.length && guard++ < 10000) {
      var a = this.actionQueue.shift();
      if (a[0].removed) continue;
      this.avm.run(a[1], a[0]);
    }
  };

  // One frame tick: advance timelines (parent first, then children, newest
  // instances first), then run the queued frame actions.
  Player.prototype.tick = function () {
    if (!this.started) {
      this.started = true;
      this.root.enterFrame(1);
    } else {
      this.stepClip(this.root);
    }
    this.initNewClips();
    this.runActions();
    this.initNewClips();
    this.runActions();
    this.updateTextBindings();
    this.updateHover();
    this.render();
  };
  Player.prototype.stepClip = function (clip) {
    var existing = clip.sortedChildren();
    clip.step();
    existing.sort(function (a, b) { return b.order - a.order; });
    for (var i = 0; i < existing.length; i++) {
      var c = existing[i];
      if (c.isClip && !c.removed && !c.fresh) this.stepClip(c);
    }
  };
  // Newly placed clips enter their first frame in the tick they appear.
  Player.prototype.initNewClips = function () {
    while (this.newClips.length) {
      var list = this.newClips; this.newClips = [];
      for (var i = 0; i < list.length; i++) {
        var c = list[i];
        if (c.removed || c.currentFrame) continue;
        c.enterFrame(1);
        if (c.totalFrames <= 1) c.playing = false;
      }
    }
  };

  // ---- Text fields bound to variables

  Player.prototype.bindText = function (o) {
    if (o.def.variableName) this.textBindings.push(o);
  };
  Player.prototype.updateTextBindings = function () {
    var self = this;
    this.textBindings = this.textBindings.filter(function (o) { return !o.removed; });
    this.textBindings.forEach(function (o) {
      var ref = self.avm.resolveVarPath(o.parent, o.def.variableName);
      if (!ref) return;
      var v = ref.obj.vars ? ref.obj.vars[ref.name] : undefined;
      if (v === undefined) {
        if (!(ref.name in ref.obj.vars)) ref.obj.vars[ref.name] = o.text; // field seeds the variable
        else o.text = self.avm.toStr(v);
      } else o.text = self.avm.toStr(v);
    });
  };

  // ---- Sound

  Player.prototype.startSound = function (clip, id, info) {
    var def = this.movie.data.sounds[id];
    if (!def) return;
    var ctx = audio.get();
    if (!ctx) return;
    var self = this;
    if (info && info.syncStop) {
      this.activeSounds = this.activeSounds.filter(function (s) { if (s.id === id) { try { s.src.stop(); } catch (e) { } return false; } return true; });
      return;
    }
    if (info && info.syncNoMultiple && this.activeSounds.some(function (s) { return s.id === id; })) return;
    // Flash drops event sounds started while audio output is unavailable.
    if (ctx.state !== "running") return;
    decodeSound(def).then(function (buf) {
      if (!buf) return;
      var src = ctx.createBufferSource();
      src.buffer = buf;
      var loops = info && info.loopCount ? info.loopCount : 1;
      var gainL = ctx.createGain(), gainR = ctx.createGain();
      var split = ctx.createChannelSplitter(2), merge = ctx.createChannelMerger(2);
      var master = ctx.createGain();
      master.gain.value = self.volume / 100;
      src.connect(split);
      // mono sources feed both channels
      if (buf.numberOfChannels === 1) { src.disconnect(); src.connect(gainL); src.connect(gainR); }
      else { split.connect(gainL, 0); split.connect(gainR, 1); }
      gainL.connect(merge, 0, 0); gainR.connect(merge, 0, 1);
      merge.connect(master); master.connect(ctx.destination);
      var t0 = ctx.currentTime;
      var start = info && info.inPoint ? info.inPoint / 44100 : 0;
      var dur = buf.duration;
      var env = info && info.envelopeRecords;
      if (env && env.length) {
        // pos44 is in 44.1kHz samples from the start of the sound; levels are 0..32768
        for (var l = 0; l < loops; l++) {
          env.forEach(function (e, i) {
            var t = t0 + l * dur + e.pos44 / 44100;
            if (i === 0 && l === 0) {
              gainL.gain.setValueAtTime(e.leftLevel / 32768, t0);
              gainR.gain.setValueAtTime(e.rightLevel / 32768, t0);
            } else {
              gainL.gain.linearRampToValueAtTime(e.leftLevel / 32768, t);
              gainR.gain.linearRampToValueAtTime(e.rightLevel / 32768, t);
            }
          });
        }
      }
      if (loops > 1) { src.loop = true; src.loopStart = start; src.loopEnd = dur; }
      src.start(t0, start, loops > 1 ? undefined : undefined);
      if (loops > 1) src.stop(t0 + loops * (dur - start));
      var rec = { id: id, src: src, master: master };
      self.activeSounds.push(rec);
      src.onended = function () { self.activeSounds = self.activeSounds.filter(function (s) { return s !== rec; }); };
    });
  };
  Player.prototype.setVolume = function (v) {
    this.volume = v;
    this.activeSounds.forEach(function (s) { s.master.gain.value = v / 100; });
  };

  // ---- Mouse & buttons

  Player.prototype.bindMouse = function () {
    var self = this, c = this.canvas;
    function pos(e) {
      var r = c.getBoundingClientRect();
      var x = ((e.clientX - r.left) * self.cssScaleX - self.devX) / self.devScale;
      var y = ((e.clientY - r.top) * self.cssScaleY - self.devY) / self.devScale;
      var f = self.movie.data.frame;
      self.mouseX = x * 20 + f[0]; self.mouseY = y * 20 + f[1];
    }
    c.addEventListener("pointermove", function (e) { pos(e); self.mouseInside = true; self.updateHover(); });
    c.addEventListener("pointerdown", function (e) {
      if (e.button !== 0) return;
      pos(e); self.mouseDown = true; self.updateHover();
      if (self.hover) { self.pressed = self.hover; self.buttonEvent(self.hover, 4, 4); }
    });
    window.addEventListener("pointerup", function (e) {
      if (e.button !== 0 || !self.mouseDown) return;
      self.mouseDown = false;
      var p = self.pressed; self.pressed = null;
      if (p) {
        if (p === self.hover) self.buttonEvent(p, 2, 8);
        else self.buttonEvent(p, 1, 64);
      }
      self.updateHover();
    });
    c.addEventListener("pointerleave", function () { self.mouseInside = false; self.updateHover(); });
  };
  Player.prototype.findButtonAt = function (x, y) {
    var ctx = this.ctx, found = null;
    var visit = function (obj, m) {
      if (!obj.visible) return;
      var mm = mmul(m, obj.matrix);
      if (obj instanceof Button) {
        for (var i = 0; i < obj.hitChildren.length; i++) if (hitTest(obj.hitChildren[i], m === null ? IDENTITY : mm, x, y, ctx, true)) { found = obj; }
        return;
      }
      if (obj.isClip) {
        var kids = obj.sortedChildren();
        for (var k = 0; k < kids.length; k++) if (!kids[k].clipDepth) visit(kids[k], mm);
      }
    };
    visit(this.root, IDENTITY);
    return found;
  };
  function hitTest(obj, parentM, x, y, ctx, shapeOnly) {
    if (!obj.visible && !shapeOnly) return false;
    var m = mmul(parentM, obj.matrix);
    var player = obj.player;
    if (obj.isClip || obj instanceof Button) {
      var kids = obj.isClip ? obj.sortedChildren() : obj.childList;
      for (var i = 0; i < kids.length; i++) if (!kids[i].clipDepth && hitTest(kids[i], m, x, y, ctx, shapeOnly)) return true;
      return false;
    }
    var inv = minv(m);
    if (!inv) return false;
    var p = mapPoint(inv, x, y);
    var b = obj.localBounds();
    if (!b || p[0] < b[0] || p[0] > b[2] || p[1] < b[1] || p[1] > b[3]) return false;
    if (obj.def.t === "s" || obj.def.t === "m") {
      var layers = obj.def.t === "s" ? player.movie.shapeLayers(obj.id) : player.movie.morphLayers(obj.id, obj.ratio);
      ctx.save(); ctx.setTransform(1, 0, 0, 1, 0, 0);
      for (var j = 0; j < layers.length; j++) {
        var L = layers[j];
        if (L.k === "f" ? ctx.isPointInPath(L.path, p[0], p[1]) : (ctx.lineWidth = Math.max(L.s.w, 20), ctx.isPointInStroke(L.path, p[0], p[1]))) { ctx.restore(); return true; }
      }
      ctx.restore();
      return false;
    }
    return true; // text: bounds hit
  }
  Player.prototype.updateHover = function () {
    var btn = this.mouseInside ? this.findButtonAt(this.mouseX, this.mouseY) : null;
    var prev = this.hover;
    if (btn !== prev) {
      this.hover = btn;
      if (this.mouseDown && this.pressed) {
        if (prev === this.pressed) this.buttonEvent(prev, 2, 16); // dragOut (state over)
        if (btn === this.pressed) this.buttonEvent(btn, 4, 32); // dragOver
      } else if (!this.mouseDown) {
        if (prev && !prev.removed) this.buttonEvent(prev, 1, 2);
        if (btn) this.buttonEvent(btn, 2, 1);
      }
      this.canvas.style.cursor = btn ? "pointer" : "";
    }
  };
  Player.prototype.buttonEvent = function (btn, newState, cond) {
    btn.setState(newState);
    var acts = btn.def.act;
    for (var i = 0; i < acts.length; i++) if (acts[i].cond & cond) this.queueAction(btn.parent, acts[i].a);
    this.initNewClips();
    this.runActions();
    this.render();
  };

  // ---- Rendering

  Player.prototype.render = function () {
    var ctx = this.ctx, d = this.movie.data;
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    var bg = this.opts.bgcolor || d.bg;
    ctx.fillStyle = cssColor([bg[0], bg[1], bg[2], 255]);
    ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
    ctx.save();
    // clip to stage (letterbox areas show the background)
    var base = this.baseMatrix();
    ctx.setTransform(base[0], base[1], base[2], base[3], base[4], base[5]);
    ctx.beginPath();
    ctx.rect(d.frame[0], d.frame[1], d.frame[2] - d.frame[0], d.frame[3] - d.frame[1]);
    ctx.clip();
    this.renderChildren(this.root.sortedChildren(), base, NO_CX);
    ctx.restore();
  };
  Player.prototype.renderChildren = function (kids, m, cx) {
    var ctx = this.ctx;
    for (var i = 0; i < kids.length; i++) {
      var c = kids[i];
      if (c.clipDepth) {
        // Mask: clip the following siblings up to clipDepth.
        ctx.save();
        var maskPath = new Path2D();
        this.collectMask(c, m, maskPath);
        ctx.setTransform(1, 0, 0, 1, 0, 0);
        ctx.clip(maskPath);
        var j = i + 1, masked = [];
        while (j < kids.length && kids[j].depth <= c.clipDepth) { if (!kids[j].clipDepth) masked.push(kids[j]); j++; }
        this.renderChildren(masked, m, cx);
        ctx.restore();
        i = j - 1;
        continue;
      }
      this.renderObject(c, m, cx);
    }
  };
  Player.prototype.collectMask = function (obj, parentM, path) {
    var m = mmul(parentM, obj.matrix);
    if (obj.isClip || obj instanceof Button) {
      var kids = obj.isClip ? obj.sortedChildren() : obj.childList;
      for (var i = 0; i < kids.length; i++) if (!kids[i].clipDepth) this.collectMask(kids[i], m, path);
      return;
    }
    var dm = new DOMMatrix(m);
    if (obj.def.t === "s" || obj.def.t === "m") {
      var layers = obj.def.t === "s" ? this.movie.shapeLayers(obj.id) : this.movie.morphLayers(obj.id, obj.ratio);
      layers.forEach(function (L) { if (L.k === "f") path.addPath(L.path, dm); });
    } else if (obj.def.t === "t") {
      var self = this;
      this.eachGlyph(obj.def, function (glyphPath, gm) { path.addPath(glyphPath, new DOMMatrix(mmul(m, gm))); });
    }
  };
  Player.prototype.renderObject = function (obj, parentM, parentCx) {
    if (!obj.visible) return;
    var m = mmul(parentM, obj.matrix);
    var cx = cxConcat(parentCx, obj.cx);
    if (cx && cx[3] <= 0 && cx[7] <= 0) return; // fully transparent
    if (obj.isClip) { this.renderChildren(obj.sortedChildren(), m, cx); return; }
    if (obj instanceof Button) { this.renderChildren(obj.childList, m, cx); return; }
    var t = obj.def.t;
    if (t === "s") this.drawLayers(this.movie.shapeLayers(obj.id), m, cx);
    else if (t === "m") this.drawLayers(this.movie.morphLayers(obj.id, obj.ratio), m, cx);
    else if (t === "t") this.drawText(obj.def, m, cx);
    else if (t === "e") this.drawEditText(obj, m, cx);
  };
  Player.prototype.drawLayers = function (layers, m, cx) {
    var ctx = this.ctx;
    var scale = Math.sqrt(Math.abs(m[0] * m[3] - m[1] * m[2])); // device px per twip
    for (var i = 0; i < layers.length; i++) {
      var L = layers[i];
      ctx.setTransform(m[0], m[1], m[2], m[3], m[4], m[5]);
      if (L.k === "f") this.fillPath(L.path, L.s, m, cx);
      else {
        var s = L.s;
        // Strokes are at least one device pixel wide, like Flash hairlines.
        ctx.lineWidth = Math.max(s.w, 1 / scale);
        ctx.lineCap = s.cap === 1 ? "butt" : s.cap === 2 ? "square" : "round";
        ctx.lineJoin = s.join === 1 ? "bevel" : s.join === 2 ? "miter" : "round";
        if (s.join === 2) ctx.miterLimit = s.ml || 3;
        var col = s.f.t === "s" ? applyCx(cx, s.f.c) : [0, 0, 0, 255];
        if (col[3] <= 0) continue;
        ctx.strokeStyle = cssColor(col);
        ctx.stroke(L.path);
      }
    }
  };
  Player.prototype.fillPath = function (path, s, m, cx) {
    var ctx = this.ctx;
    if (s.t === "s" || s.t === "glyph") {
      var c = applyCx(cx, s.c);
      if (c[3] <= 0) return;
      ctx.fillStyle = cssColor(c);
      ctx.fill(path);
      return;
    }
    // Gradient/bitmap fills live in their own coordinate space (s.m). Draw the
    // path pre-transformed by the inverse so the fill style can use that space.
    var inv = minv(s.m);
    if (!inv) return;
    var p2 = new Path2D();
    p2.addPath(path, new DOMMatrix(inv));
    ctx.transform(s.m[0], s.m[1], s.m[2], s.m[3], s.m[4], s.m[5]);
    if (s.t === "bm") {
      var img = this.bitmapFor(s.id, cx);
      if (!img) return;
      var pat = ctx.createPattern(img, s.rep ? "repeat" : "no-repeat");
      // Flash Player only smooths bitmap fills from SWF 8 on.
      ctx.imageSmoothingEnabled = !!s.sm && this.movie.data.swfVersion >= 8;
      ctx.imageSmoothingQuality = "low"; // bilinear, like Flash/Ruffle
      ctx.fillStyle = pat;
      if (!s.rep) {
        // Clipped bitmaps: draw directly to avoid pattern edge bleeding.
        ctx.save();
        ctx.clip(p2);
        ctx.drawImage(img, 0, 0);
        ctx.restore();
      } else ctx.fill(p2);
      ctx.globalAlpha = 1;
      return;
    }
    var g;
    if (s.t === "lg") g = ctx.createLinearGradient(-16384, 0, 16384, 0);
    else g = ctx.createRadialGradient(s.t === "fg" ? s.focal * 16384 : 0, 0, 0, 0, 0, 16384);
    for (var i = 0; i < s.st.length; i++) {
      var st = s.st[i];
      g.addColorStop(st[0] / 255, cssColor(applyCx(cx, [st[1], st[2], st[3], st[4]])));
    }
    ctx.fillStyle = g;
    ctx.fill(p2);
  };
  Player.prototype.bitmapNeedsCx = function (cx) {
    return cx && (cx[0] !== 256 || cx[1] !== 256 || cx[2] !== 256 || cx[4] || cx[5] || cx[6] || cx[7]);
  };
  // Bitmaps with a colour transform are recoloured once and cached.
  Player.prototype.bitmapFor = function (id, cx) {
    var img = this.movie.images[id];
    if (!img) return null;
    if (!cx) { this.ctx.globalAlpha = 1; return img; }
    if (!this.bitmapNeedsCx(cx)) { this.ctx.globalAlpha = Math.max(0, Math.min(1, cx[3] / 256)); return img; }
    this.ctx.globalAlpha = 1;
    var key = id + ":" + cx.join(",");
    var cache = this.movie.cxCache || (this.movie.cxCache = {});
    if (cache[key]) return cache[key];
    var c = document.createElement("canvas");
    c.width = img.width; c.height = img.height;
    var g = c.getContext("2d");
    g.drawImage(img, 0, 0);
    var id2 = g.getImageData(0, 0, c.width, c.height), p = id2.data;
    for (var i = 0; i < p.length; i += 4) {
      p[i] = clamp255(p[i] * cx[0] / 256 + cx[4]);
      p[i + 1] = clamp255(p[i + 1] * cx[1] / 256 + cx[5]);
      p[i + 2] = clamp255(p[i + 2] * cx[2] / 256 + cx[6]);
      p[i + 3] = clamp255(p[i + 3] * cx[3] / 256 + cx[7]);
    }
    g.putImageData(id2, 0, 0);
    var keys = Object.keys(cache);
    if (keys.length > 256) delete cache[keys[0]];
    return (cache[key] = c);
  };

  // ---- Text

  Player.prototype.glyphPath = function (fontId, index) {
    var f = this.movie.chars[fontId];
    if (!f || !f.gl[index]) return null;
    f._paths = f._paths || [];
    return f._paths[index] || (f._paths[index] = makePath(f.gl[index]));
  };
  Player.prototype.eachGlyph = function (def, fn) {
    var font = null, size = 0, color = [0, 0, 0, 255], x = 0, y = 0;
    for (var i = 0; i < def.recs.length; i++) {
      var r = def.recs[i];
      if (r.f !== undefined) font = r.f;
      if (r.sz !== undefined) size = r.sz;
      if (r.c) color = r.c;
      if (r.x !== undefined) x = r.x;
      if (r.y !== undefined) y = r.y;
      var f = this.movie.chars[font];
      var k = f ? size / f.em : 0;
      for (var g = 0; g < r.g.length; g++) {
        var p = this.glyphPath(font, r.g[g][0]);
        if (p) fn(p, mmul(def.m, [k, 0, 0, k, x, y]), color);
        x += r.g[g][1];
      }
    }
  };
  Player.prototype.drawText = function (def, m, cx) {
    var ctx = this.ctx;
    this.eachGlyph(def, function (p, gm, color) {
      var c = applyCx(cx, color);
      if (c[3] <= 0) return;
      var mm = mmul(m, gm);
      ctx.setTransform(mm[0], mm[1], mm[2], mm[3], mm[4], mm[5]);
      ctx.fillStyle = cssColor(c);
      ctx.fill(p);
    });
  };
  Player.prototype.drawEditText = function (obj, m, cx) {
    var def = obj.def, text = obj.text;
    if (!text) return;
    var font = this.movie.chars[def.fontId];
    if (!font || !font.codes) return;
    var ctx = this.ctx, size = def.fontSize, k = size / font.em;
    var color = applyCx(cx, def.color || [0, 0, 0, 255]);
    if (color[3] <= 0) return;
    var b = def.b;
    // Single-line layout with embedded glyphs (2px gutter as in Flash).
    var ascent = font.asc !== undefined ? font.asc * k : size * 0.9;
    var x = b[0] + 40 + (def.marginLeft || 0) + (def.indent || 0);
    var y = b[1] + 40 + ascent;
    var lineH = ((font.asc || 0) + (font.desc || 0)) * k + (def.leading || 0);
    var lines = String(text).split(/\r\n|\r|\n/);
    if (!def.multiline) lines = [lines.join(" ")];
    ctx.save();
    ctx.setTransform(m[0], m[1], m[2], m[3], m[4], m[5]);
    ctx.beginPath(); ctx.rect(b[0], b[1], b[2] - b[0], b[3] - b[1]); ctx.clip();
    ctx.fillStyle = cssColor(color);
    for (var li = 0; li < lines.length; li++) {
      var line = lines[li], width = 0, glyphs = [];
      for (var i = 0; i < line.length; i++) {
        var gi = font.codes.indexOf(line.charCodeAt(i));
        var adv = gi >= 0 && font.adv ? font.adv[gi] * k : size / 2;
        glyphs.push([gi, width]);
        width += adv;
      }
      var ox = x;
      var avail = b[2] - b[0] - 80 - (def.marginLeft || 0) - (def.marginRight || 0);
      if (def.align === 1) ox = x + (avail - width);
      else if (def.align === 2) ox = x + (avail - width) / 2;
      for (var g = 0; g < glyphs.length; g++) {
        if (glyphs[g][0] < 0) continue;
        var p = this.glyphPath(def.fontId, glyphs[g][0]);
        if (!p) continue;
        var mm = mmul(m, [k, 0, 0, k, ox + glyphs[g][1], y + li * lineH]);
        ctx.setTransform(mm[0], mm[1], mm[2], mm[3], mm[4], mm[5]);
        ctx.fill(p);
      }
    }
    ctx.restore();
  };

  // ---- Main loop

  Player.prototype.start = function () {
    var self = this, interval = 1000 / (this.movie.data.rate || 12), next = performance.now();
    this.avm = this.avm || new AVM1(this);
    this.tick();
    next += interval;
    if (config.manual) return; // test harness drives tick() itself
    var loop = function (now) {
      // Catch up at most a few frames (e.g. after the tab was hidden).
      var n = 0;
      while (now >= next && n < 4) { self.tick(); next += interval; n++; }
      if (now - next > interval * 4) next = now + interval;
      requestAnimationFrame(loop);
    };
    requestAnimationFrame(loop);
  };

  // -------------------------------------------------------------------------
  // AVM1 interpreter (SWF 6 semantics, the opcodes these movies use)

  var PROPS = ["_x", "_y", "_xscale", "_yscale", "_currentframe", "_totalframes", "_alpha", "_visible", "_width", "_height",
    "_rotation", "_target", "_framesloaded", "_name", "_droptarget", "_url", "_highquality", "_focusrect", "_soundbuftime",
    "_quality", "_xmouse", "_ymouse"];

  function AVM1(player) {
    this.player = player;
    var self = this;
    this.builtins = {
      Sound: function (target) { return new SoundObject(self.player, target); },
      Object: function () { return {}; },
      Array: function () { return Array.prototype.slice.call(arguments); }
    };
    this.system = { useCodepage: false, capabilities: {} };
  }

  function SoundObject(player, target) { this.player = player; this.target = target; }
  SoundObject.prototype.getVolume = function () { return this.player.volume; };
  SoundObject.prototype.setVolume = function (v) { this.player.setVolume(Number(v)); };
  SoundObject.prototype.stop = function () { this.player.activeSounds.forEach(function (s) { try { s.src.stop(); } catch (e) { } }); };
  SoundObject.prototype.start = function () { };
  SoundObject.prototype.attachSound = function () { };
  SoundObject.prototype.getPan = function () { return 0; };
  SoundObject.prototype.setPan = function () { };

  AVM1.prototype.toNum = function (v) {
    if (typeof v === "number") return v;
    if (v === undefined || v === null) return 0; // SWF < 7
    if (typeof v === "boolean") return v ? 1 : 0;
    if (typeof v === "string") {
      if (v === "") return NaN;
      var s = v.trim();
      if (/^0x[0-9a-f]+$/i.test(s)) return parseInt(s, 16);
      var n = Number(s);
      return isNaN(n) ? NaN : n;
    }
    if (v instanceof MovieClip) return NaN;
    return NaN;
  };
  AVM1.prototype.toStr = function (v) {
    if (v === undefined) return ""; // SWF < 7
    if (v === null) return "null";
    if (typeof v === "boolean") return v ? "true" : "false";
    if (typeof v === "number") {
      if (isNaN(v)) return "NaN";
      if (!isFinite(v)) return v > 0 ? "Infinity" : "-Infinity";
      return String(v);
    }
    if (v instanceof DisplayObject) return v.targetPath();
    if (typeof v === "object") return "[object Object]";
    return String(v);
  };
  AVM1.prototype.toBool = function (v) {
    if (typeof v === "boolean") return v;
    if (typeof v === "number") return v !== 0 && !isNaN(v);
    if (typeof v === "string") { var n = this.toNum(v); return n !== 0 && !isNaN(n); } // SWF 6
    if (v === undefined || v === null) return false;
    return true;
  };
  AVM1.prototype.equals2 = function (a, b) {
    var ta = typeof a, tb = typeof b;
    if ((a === undefined || a === null) && (b === undefined || b === null)) return true;
    if (a === undefined || a === null || b === undefined || b === null) return false;
    if (ta === tb && ta !== "object") return a === b;
    if (ta === "object" || tb === "object") return a === b;
    if (ta === "boolean") return this.equals2(a ? 1 : 0, b);
    if (tb === "boolean") return this.equals2(a, b ? 1 : 0);
    return this.toNum(a) === this.toNum(b);
  };
  AVM1.prototype.add2 = function (a, b) {
    if (typeof a === "string" || typeof b === "string") return this.toStr(a) + this.toStr(b);
    return this.toNum(a) + this.toNum(b);
  };
  AVM1.prototype.less2 = function (a, b) {
    if (typeof a === "string" && typeof b === "string") return a < b;
    var x = this.toNum(a), y = this.toNum(b);
    if (isNaN(x) || isNaN(y)) return undefined;
    return x < y;
  };

  // Resolve a target path ("_root.a.b", "/a/b", "../a", "") to a display object.
  AVM1.prototype.resolveTarget = function (base, path) {
    if (path instanceof DisplayObject) return path;
    path = this.toStr(path);
    if (path === "") return base;
    var obj = base, parts;
    if (path.charAt(0) === "/") { obj = this.player.root; path = path.slice(1); }
    parts = path.split(/[.\/]|:/).filter(function (p) { return p !== ""; });
    for (var i = 0; i < parts.length; i++) {
      var p = parts[i];
      if (p === "_root" || p === "_level0") obj = this.player.root;
      else if (p === "_parent" || p === "..") obj = obj && obj.parent;
      else if (p === "this") { /* stay */ }
      else obj = obj && obj.isClip ? obj.childByName(p) : null;
      if (!obj) return null;
    }
    return obj;
  };
  // For "path:var" or "a.b.var" variable references.
  AVM1.prototype.resolveVarPath = function (base, name) {
    var m = /^(.*)[:.]([^:.]+)$/.exec(name);
    if (!m) return { obj: base, name: name };
    var t = this.resolveTarget(base, m[1]);
    if (!t || !t.isClip) return null;
    return { obj: t, name: m[2] };
  };

  AVM1.prototype.getVariable = function (scope, name) {
    name = this.toStr(name);
    if (/[:.\/]/.test(name)) {
      var t = this.resolveTarget(scope.target, name);
      if (t) return t;
      var r = this.resolveVarPath(scope.target, name);
      return r ? this.getMember(r.obj, r.name) : undefined;
    }
    var lname = name.toLowerCase();
    if (lname === "this") return scope.target;
    if (lname === "_root" || lname === "_level0") return this.player.root;
    if (lname === "_parent") return scope.target.parent || undefined;
    if (lname === "_global") return this.player.globals;
    var t2 = scope.target;
    if (name in t2.vars) return t2.vars[name];
    var child = t2.childByName(name);
    if (child) return child;
    if (PROPS.indexOf(lname) >= 0) return this.getProp(t2, PROPS.indexOf(lname));
    if (name in this.player.globals) return this.player.globals[name];
    if (name === "System") return this.system;
    if (name in this.builtins) return this.builtins[name];
    return undefined;
  };
  AVM1.prototype.setVariable = function (scope, name, value) {
    name = this.toStr(name);
    var r = this.resolveVarPath(scope.target, name);
    if (!r) return;
    this.setMember(r.obj, r.name, value);
  };
  AVM1.prototype.getMember = function (obj, name) {
    if (obj === undefined || obj === null) return undefined;
    name = this.toStr(name);
    if (obj instanceof DisplayObject) {
      var idx = PROPS.indexOf(name.toLowerCase());
      if (idx >= 0) return this.getProp(obj, idx);
      if (obj.isClip) {
        if (name in obj.vars) return obj.vars[name];
        var c = obj.childByName(name);
        if (c) return c;
        if (name === "_parent") return obj.parent || undefined;
      }
      if (obj instanceof EditText && name === "text") return obj.text;
      return undefined;
    }
    if (typeof obj === "object" || typeof obj === "function") {
      var v = obj[name];
      return typeof v === "function" ? v.bind(obj) : v;
    }
    if (typeof obj === "string" && name === "length") return obj.length;
    return undefined;
  };
  AVM1.prototype.setMember = function (obj, name, value) {
    if (obj === undefined || obj === null) return;
    name = this.toStr(name);
    if (obj instanceof DisplayObject) {
      var idx = PROPS.indexOf(name.toLowerCase());
      if (idx >= 0) { this.setProp(obj, idx, value); return; }
      if (obj instanceof EditText && name === "text") { obj.text = this.toStr(value); return; }
      if (obj.isClip) obj.vars[name] = value;
      return;
    }
    if (typeof obj === "object") obj[name] = value;
  };

  // Matrix decomposition helpers for _xscale/_yscale/_rotation.
  function decompose(m) {
    var sx = Math.sqrt(m[0] * m[0] + m[1] * m[1]);
    var sy = Math.sqrt(m[2] * m[2] + m[3] * m[3]);
    if (m[0] * m[3] - m[1] * m[2] < 0) sy = -sy;
    var rot = Math.atan2(m[1], m[0]);
    return { sx: sx, sy: sy, rot: rot, skew: Math.atan2(-m[2], m[3]) - rot };
  }
  function compose(d, tx, ty) {
    var c = Math.cos(d.rot), s = Math.sin(d.rot), c2 = Math.cos(d.rot + d.skew), s2 = Math.sin(d.rot + d.skew);
    return [d.sx * c, d.sx * s, -d.sy * s2, d.sy * c2, tx, ty];
  }

  AVM1.prototype.getProp = function (o, idx) {
    var m = o.matrix, d;
    switch (idx) {
      case 0: return Math.round(m[4]) / 20;
      case 1: return Math.round(m[5]) / 20;
      case 2: d = decompose(m); return d.sx * 100;
      case 3: d = decompose(m); return d.sy * 100;
      case 4: return o.isClip ? Math.max(1, o.currentFrame) : 1;
      case 5: return o.isClip ? o.totalFrames : 1;
      case 6: return o.cx ? o.cx[3] / 256 * 100 : 100;
      case 7: return o.visible;
      case 8: case 9: {
        var b = o.parent ? o.boundsIn(IDENTITY) : o.boundsIn(IDENTITY);
        if (!b) return 0;
        return Math.round((idx === 8 ? b[2] - b[0] : b[3] - b[1])) / 20;
      }
      case 10: d = decompose(m); return d.rot * 180 / Math.PI;
      case 11: return o.parent ? o.targetPath().replace(/^_level0/, "").replace(/\./g, "/") || "/" : "/";
      case 12: return o.isClip ? o.totalFrames : 1;
      case 13: return o.name;
      case 14: return "";
      case 15: return this.player.movie.url;
      case 16: return 1;
      case 17: return true;
      case 18: return 5;
      case 19: return "HIGH";
      case 20: case 21: {
        var inv = minv(o.worldMatrix());
        if (!inv) return 0;
        var p = mapPoint(inv, this.player.mouseX, this.player.mouseY);
        return Math.round(idx === 20 ? p[0] : p[1]) / 20;
      }
    }
    return undefined;
  };
  AVM1.prototype.setProp = function (o, idx, v) {
    var m = o.matrix.slice(), n = this.toNum(v), d;
    if (idx !== 7 && idx !== 13 && isNaN(n)) return;
    switch (idx) {
      case 0: m[4] = Math.round(n * 20); break;
      case 1: m[5] = Math.round(n * 20); break;
      case 2: d = decompose(m); d.sx = n / 100; m = compose(d, m[4], m[5]); break;
      case 3: d = decompose(m); d.sy = n / 100; m = compose(d, m[4], m[5]); break;
      case 6: {
        var cx = o.cx ? o.cx.slice() : [256, 256, 256, 256, 0, 0, 0, 0];
        cx[3] = n * 256 / 100;
        o.cx = cx;
        o.scripted = true;
        return;
      }
      case 7: o.visible = this.toBool(v); return;
      case 8: case 9: {
        var b = o.localBounds();
        if (!b) return;
        var size = idx === 8 ? b[2] - b[0] : b[3] - b[1];
        if (!size) return;
        d = decompose(m);
        // Flash: new scale = target size / untransformed size (rotation ignored for these movies)
        if (idx === 8) d.sx = (n * 20) / size * (d.sx < 0 ? -1 : 1);
        else d.sy = (n * 20) / size * (d.sy < 0 ? -1 : 1);
        m = compose(d, m[4], m[5]);
        break;
      }
      case 10: d = decompose(m); d.rot = n * Math.PI / 180; m = compose(d, m[4], m[5]); break;
      case 13: o.name = this.toStr(v); return;
      default: return;
    }
    o.matrix = m;
    o.scripted = true;
  };

  AVM1.prototype.getURL = function (scope, url, target, method, loadVars) {
    url = this.toStr(url); target = this.toStr(target);
    var player = this.player;
    if (/^fscommand:/i.test(url)) {
      var cmd = url.slice(10), id = player.opts.id;
      var fn = id && window[id + "_DoFSCommand"];
      if (typeof fn === "function") { try { fn(cmd, target); } catch (e) { if (window.console) console.error(e); } }
      return;
    }
    if (loadVars) {
      var t = this.resolveTarget(scope.target, target);
      if (!t || !t.isClip) return;
      var abs = new URL(url, player.movie.url).href;
      fetch(abs).then(function (r) { return r.ok ? r.arrayBuffer() : null; }).then(function (buf) {
        if (!buf || t.removed) return;
        var enc = player.avm.system.useCodepage ? (document.characterSet || "utf-8") : "utf-8";
        var text;
        try { text = new TextDecoder(enc).decode(buf); } catch (e) { text = new TextDecoder().decode(buf); }
        text.replace(/^﻿/, "").split("&").forEach(function (pair) {
          if (!pair) return;
          var i = pair.indexOf("="), k = i < 0 ? pair : pair.slice(0, i), v = i < 0 ? "" : pair.slice(i + 1);
          try { t.vars[decodeURIComponent(k.replace(/\+/g, " "))] = decodeURIComponent(v.replace(/\+/g, " ")); }
          catch (e) { t.vars[k] = v; }
        });
      }).catch(function () { });
      return;
    }
    if (/^_level\d+$/.test(target)) return; // loadMovie: not used
    var href = new URL(url, document.baseURI).href;
    if (!target || target === "_self") window.location.href = href;
    else if (target === "_top") window.top.location.href = href;
    else if (target === "_parent") window.parent.location.href = href;
    else window.open(href, target);
  };

  AVM1.prototype.run = function (code, target) {
    if (typeof code === "string") code = (this._decoded || (this._decoded = {}))[code] || (this._decoded[code] = b64bytes(code));
    var scope = { target: target, origTarget: target };
    var stack = [], pool = [], regs = [undefined, undefined, undefined, undefined];
    var dv = new DataView(code.buffer, code.byteOffset, code.byteLength);
    var pc = 0, self = this, steps = 0;
    var pop = function () { return stack.length ? stack.pop() : undefined; };
    var cstr = function (p) { var s = p; while (code[p]) p++; return [utf8(code.subarray(s, p)), p + 1]; };
    while (pc < code.length && steps++ < 100000) {
      var op = code[pc++];
      if (op === 0) break;
      var len = 0, start = pc;
      if (op >= 0x80) { len = dv.getUint16(pc, true); pc += 2; start = pc; pc += len; }
      var a, b, t;
      switch (op) {
        case 0x04: if (scope.target.isClip) scope.target.gotoFrame(scope.target.currentFrame + 1, true); break; // NextFrame
        case 0x05: if (scope.target.isClip) scope.target.gotoFrame(scope.target.currentFrame - 1, true); break; // PrevFrame
        case 0x06: if (scope.target.isClip) scope.target.playing = true; break; // Play
        case 0x07: if (scope.target.isClip) scope.target.playing = false; break; // Stop
        case 0x08: break; // ToggleQuality
        case 0x09: this.player.activeSounds.forEach(function (s) { try { s.src.stop(); } catch (e) { } }); break;
        case 0x0A: b = pop(); a = pop(); stack.push(this.toNum(a) + this.toNum(b)); break;
        case 0x0B: b = pop(); a = pop(); stack.push(this.toNum(a) - this.toNum(b)); break;
        case 0x0C: b = pop(); a = pop(); stack.push(this.toNum(a) * this.toNum(b)); break;
        case 0x0D: b = pop(); a = pop(); b = this.toNum(b); stack.push(b === 0 ? "#ERROR#" : this.toNum(a) / b); break;
        case 0x0E: b = pop(); a = pop(); stack.push(this.toNum(a) === this.toNum(b)); break;
        case 0x0F: b = pop(); a = pop(); stack.push(this.toNum(a) < this.toNum(b)); break;
        case 0x10: b = pop(); a = pop(); stack.push(this.toBool(a) && this.toBool(b)); break;
        case 0x11: b = pop(); a = pop(); stack.push(this.toBool(a) || this.toBool(b)); break;
        case 0x12: stack.push(!this.toBool(pop())); break;
        case 0x13: b = pop(); a = pop(); stack.push(this.toStr(a) === this.toStr(b)); break;
        case 0x14: case 0x31: stack.push(this.toStr(pop()).length); break;
        case 0x15: case 0x35: { var cnt = this.toNum(pop()), idx = this.toNum(pop()), s = this.toStr(pop()); stack.push(s.substr(Math.max(0, idx - 1), cnt)); break; }
        case 0x17: pop(); break;
        case 0x18: a = this.toNum(pop()); stack.push(a < 0 ? Math.ceil(a) : Math.floor(a)); break;
        case 0x1C: stack.push(this.getVariable(scope, pop())); break;
        case 0x1D: b = pop(); a = pop(); this.setVariable(scope, a, b); break;
        case 0x20: { a = pop(); t = a instanceof DisplayObject ? a : this.resolveTarget(scope.origTarget, a); scope.target = t || scope.origTarget; break; } // SetTarget2
        case 0x21: b = pop(); a = pop(); stack.push(this.toStr(a) + this.toStr(b)); break;
        case 0x22: { var pi = this.toNum(pop()); a = pop(); t = this.resolveTarget(scope.target, a); stack.push(t ? this.getProp(t, pi) : undefined); break; }
        case 0x23: { var val = pop(), pidx = this.toNum(pop()); a = pop(); t = this.resolveTarget(scope.target, a); if (t) this.setProp(t, pidx, val); break; }
        case 0x26: pop(); break; // Trace
        case 0x29: b = pop(); a = pop(); stack.push(this.toStr(a) < this.toStr(b)); break;
        case 0x30: { a = this.toNum(pop()); stack.push(a > 0 ? Math.floor(Math.random() * a) : 0); break; }
        case 0x32: case 0x36: stack.push(this.toStr(pop()).charCodeAt(0) || 0); break;
        case 0x33: case 0x37: stack.push(String.fromCharCode(this.toNum(pop()))); break;
        case 0x34: stack.push(Math.round(performance.now())); break;
        case 0x3C: b = pop(); a = pop(); scope.target.vars && (scope.target.vars[this.toStr(a)] = b); break; // DefineLocal (timeline scope)
        case 0x41: a = pop(); if (scope.target.vars && !(this.toStr(a) in scope.target.vars)) scope.target.vars[this.toStr(a)] = undefined; break;
        case 0x3A: { b = pop(); a = pop(); if (a && typeof a === "object") { if (a instanceof MovieClip) delete a.vars[this.toStr(b)]; else delete a[this.toStr(b)]; } stack.push(true); break; }
        case 0x3B: { a = this.toStr(pop()); if (scope.target.vars) delete scope.target.vars[a]; stack.push(true); break; }
        case 0x3D: { // CallFunction
          var fname = this.toStr(pop()), nargs = this.toNum(pop()), args = [];
          for (var i = 0; i < nargs; i++) args.push(pop());
          var fn = this.getVariable(scope, fname);
          stack.push(typeof fn === "function" ? fn.apply(null, args) : undefined);
          break;
        }
        case 0x3E: pc = code.length; break; // Return
        case 0x3F: b = pop(); a = pop(); stack.push(this.toNum(a) % this.toNum(b)); break;
        case 0x40: { // NewObject
          var cname = this.toStr(pop()), na = this.toNum(pop()), ca = [];
          for (var j = 0; j < na; j++) ca.push(pop());
          var ctor = this.getVariable(scope, cname);
          stack.push(typeof ctor === "function" ? ctor.apply(null, ca) : {});
          break;
        }
        case 0x42: { var n2 = this.toNum(pop()), arr = []; for (var q = 0; q < n2; q++) arr.push(pop()); stack.push(arr); break; }
        case 0x43: { var n3 = this.toNum(pop()), ob = {}; for (var w = 0; w < n3; w++) { var vv = pop(); ob[this.toStr(pop())] = vv; } stack.push(ob); break; }
        case 0x44: { a = pop(); stack.push(a instanceof MovieClip ? "movieclip" : a === null ? "null" : typeof a === "function" ? "function" : typeof a); break; }
        case 0x45: { a = pop(); stack.push(a instanceof DisplayObject ? this.getProp(a, 11) : undefined); break; }
        case 0x47: b = pop(); a = pop(); stack.push(this.add2(a, b)); break;
        case 0x48: b = pop(); a = pop(); stack.push(this.less2(a, b)); break;
        case 0x49: b = pop(); a = pop(); stack.push(this.equals2(a, b)); break;
        case 0x4A: stack.push(this.toNum(pop())); break;
        case 0x4B: stack.push(this.toStr(pop())); break;
        case 0x4C: a = pop(); stack.push(a, a); break;
        case 0x4D: b = pop(); a = pop(); stack.push(b, a); break;
        case 0x4E: b = pop(); a = pop(); stack.push(this.getMember(a, b)); break;
        case 0x4F: { var v3 = pop(); b = pop(); a = pop(); this.setMember(a, b, v3); break; }
        case 0x50: stack.push(this.toNum(pop()) + 1); break;
        case 0x51: stack.push(this.toNum(pop()) - 1); break;
        case 0x52: { // CallMethod
          var mname = pop(), obj = pop(), nm = this.toNum(pop()), ma = [];
          for (var z = 0; z < nm; z++) ma.push(pop());
          var f = (mname === undefined || mname === "") ? obj : (obj !== undefined && obj !== null ? obj[this.toStr(mname)] : undefined);
          stack.push(typeof f === "function" ? f.apply(obj, ma) : undefined);
          break;
        }
        case 0x60: b = pop(); a = pop(); stack.push(this.toNum(a) & this.toNum(b)); break;
        case 0x61: b = pop(); a = pop(); stack.push(this.toNum(a) | this.toNum(b)); break;
        case 0x62: b = pop(); a = pop(); stack.push(this.toNum(a) ^ this.toNum(b)); break;
        case 0x63: b = pop(); a = pop(); stack.push(this.toNum(a) << this.toNum(b)); break;
        case 0x64: b = pop(); a = pop(); stack.push(this.toNum(a) >> this.toNum(b)); break;
        case 0x65: b = pop(); a = pop(); stack.push(this.toNum(a) >>> this.toNum(b)); break;
        case 0x66: b = pop(); a = pop(); stack.push(a === b); break;
        case 0x67: b = pop(); a = pop(); { var lr = this.less2(b, a); stack.push(lr === undefined ? false : lr); } break;
        case 0x68: b = pop(); a = pop(); stack.push(this.toStr(a) > this.toStr(b)); break;
        case 0x81: if (scope.target.isClip) scope.target.gotoFrame(dv.getUint16(start, true) + 1, true); break; // GotoFrame (stops)
        case 0x83: { var u = cstr(start), tg = cstr(u[1]); this.getURL(scope, u[0], tg[0], 0, false); break; }
        case 0x87: regs[code[start]] = stack[stack.length - 1]; break;
        case 0x88: { var cnt2 = dv.getUint16(start, true), pp = start + 2; pool = []; for (var e = 0; e < cnt2; e++) { var r = cstr(pp); pool.push(r[0]); pp = r[1]; } break; }
        case 0x8A: break; // WaitForFrame: everything is loaded
        case 0x8D: pop(); break; // WaitForFrame2
        case 0x8B: { var tn = cstr(start)[0]; t = tn === "" ? scope.origTarget : this.resolveTarget(scope.origTarget, tn); scope.target = t || scope.origTarget; break; }
        case 0x8C: { // GoToLabel
          var lbl = cstr(start)[0].toLowerCase(), cl = scope.target;
          if (cl.isClip && cl.labels[lbl]) cl.gotoFrame(cl.labels[lbl], true);
          break;
        }
        case 0x96: { // Push
          var p = start, end = start + len;
          while (p < end) {
            var ty = code[p++];
            switch (ty) {
              case 0: { var sr = cstr(p); stack.push(sr[0]); p = sr[1]; break; }
              case 1: stack.push(dv.getFloat32(p, true)); p += 4; break;
              case 2: stack.push(null); break;
              case 3: stack.push(undefined); break;
              case 4: stack.push(regs[code[p++]]); break;
              case 5: stack.push(!!code[p++]); break;
              case 6: { var hi = dv.getUint32(p, true), lo = dv.getUint32(p + 4, true); var tmp = new DataView(new ArrayBuffer(8)); tmp.setUint32(0, hi); tmp.setUint32(4, lo); stack.push(tmp.getFloat64(0)); p += 8; break; }
              case 7: stack.push(dv.getInt32(p, true)); p += 4; break;
              case 8: stack.push(pool[code[p++]]); break;
              case 9: stack.push(pool[dv.getUint16(p, true)]); p += 2; break;
              default: p = end;
            }
          }
          break;
        }
        case 0x99: pc += dv.getInt16(start, true); break; // Jump
        case 0x9A: { // GetURL2
          var flags = code[start];
          b = pop(); a = pop();
          this.getURL(scope, a, b, flags & 3, !!(flags & 0x80));
          break;
        }
        case 0x9D: if (this.toBool(pop())) pc += dv.getInt16(start, true); break; // If
        case 0x9E: { // Call: run a frame's actions
          a = pop();
          var cf = scope.target;
          if (cf.isClip) {
            var fr = typeof a === "number" ? a : (cf.labels[this.toStr(a).toLowerCase()] || parseInt(this.toStr(a), 10));
            var fd = cf.frames[fr - 1];
            if (fd && fd.a) fd.a.forEach(function (c) { self.run(c, cf); });
          }
          break;
        }
        case 0x9F: { // GotoFrame2
          var fl = code[start], bias = fl & 2 ? dv.getUint16(start + 1, true) : 0;
          a = pop();
          var gt = scope.target;
          if (typeof a === "string" && /[:\/]/.test(a)) {
            var ci = a.lastIndexOf(":"); gt = this.resolveTarget(scope.target, a.slice(0, ci)); a = a.slice(ci + 1);
          }
          if (gt && gt.isClip) {
            var fnum = typeof a === "number" ? a : (gt.labels[this.toStr(a).toLowerCase()] || this.toNum(a));
            if (!isNaN(fnum)) gt.gotoFrame(fnum + bias, !(fl & 1));
          }
          break;
        }
        default:
          // Unsupported opcode: stop executing this block safely.
          if (window.console) console.warn("flashplayer: unsupported AVM1 op 0x" + op.toString(16));
          pc = code.length;
      }
    }
  };
  function utf8(bytes) {
    try { return new TextDecoder("utf-8", { fatal: true }).decode(bytes); }
    catch (e) { var s = ""; for (var i = 0; i < bytes.length; i++) s += String.fromCharCode(bytes[i]); return s; }
  }

  // -------------------------------------------------------------------------
  // Page integration

  var FLASH_TYPE = "application/x-shockwave-flash";
  var cache = {};

  // url is the movie's .swf.json file (or a legacy .swf URL, whose converted
  // .json sits next to it). Movie.url stays the .swf URL so relative loads
  // (loadVariables) resolve exactly as they did for the original movie.
  function loadMovie(url) {
    var json = /\.json$/i.test(url) ? url : url + ".json";
    var swf = json.replace(/\.json$/i, "");
    if (!cache[json]) {
      cache[json] = fetch(json).then(function (r) {
        if (!r.ok) throw new Error("flashplayer: cannot load " + json);
        return r.json();
      }).then(function (data) { return new Movie(data, swf).load(); });
    }
    return cache[json];
  }

  // The Flash Player scripting methods pages used to call on the movie element
  // (document.menu.GotoFrame(3) and so on). Frame numbers are 0-based here.
  function addScriptingApi(host, player) {
    var root = function () { return player.root; };
    host.GotoFrame = function (n) { root().gotoFrame((n | 0) + 1, true); };
    host.Play = function () { root().playing = true; };
    host.StopPlay = function () { root().playing = false; };
    host.Rewind = function () { root().gotoFrame(1, true); };
    host.IsPlaying = function () { return !!root().playing; };
    host.CurrentFrame = function () { return root().currentFrame - 1; };
    host.TotalFrames = function () { return root().totalFrames; };
    host.PercentLoaded = function () { return 100; };
    host.SetVariable = function (name, value) { player.avm.setVariable({ target: root() }, String(name), String(value)); };
    host.GetVariable = function (name) {
      var v = player.avm.getVariable({ target: root() }, String(name));
      return v === undefined ? null : player.avm.toStr(v);
    };
  }

  // Shared start-up for both the static <flash-player> markup and legacy
  // <embed>/<object> tags.
  function startPlayer(host, url, bg, id) {
    loadMovie(url).then(function (movie) {
      var player = new Player(host, movie, { bgcolor: bg, id: id });
      host.flashPlayer = player;
      player.avm = new AVM1(player);
      addScriptingApi(host, player);
      player.start();
    }).catch(function (e) { if (window.console) console.error(e); });
  }

  // <flash-player src="movie.swf.json" width height bgcolor name> inside an
  // optional <flash-object id> wrapper. The markup already carries its final
  // layout styles, so nothing moves when the player starts.
  function initStatic(host) {
    if (host.__flashReplaced) return;
    var src = host.getAttribute("src");
    if (!src) return;
    host.__flashReplaced = true;
    var wrap = host.parentElement && host.parentElement.tagName === "FLASH-OBJECT" ? host.parentElement : null;
    var id = (wrap && wrap.id) || host.getAttribute("name") || host.id || null;
    startPlayer(host, new URL(src, document.baseURI).href, parseColor(host.getAttribute("bgcolor")), id);
  }

  function parseColor(s) {
    if (!s) return null;
    var m = /^#?([0-9a-f]{6})$/i.exec(s.trim());
    if (!m) return null;
    var n = parseInt(m[1], 16);
    return [n >> 16, (n >> 8) & 255, n & 255, 255];
  }

  function paramsOf(el) {
    var p = {};
    if (el.tagName === "OBJECT") {
      el.querySelectorAll(":scope > param").forEach(function (x) { p[(x.getAttribute("name") || "").toLowerCase()] = x.getAttribute("value"); });
    } else {
      for (var i = 0; i < el.attributes.length; i++) p[el.attributes[i].name.toLowerCase()] = el.attributes[i].value;
    }
    return p;
  }

  function dim(v) {
    if (v === null || v === undefined || v === "") return null;
    return /^\d+(\.\d+)?$/.test(v) ? v + "px" : v;
  }

  function replace(el) {
    if (el.__flashReplaced) return;
    el.__flashReplaced = true;
    var params = paramsOf(el);
    var outer = el.tagName === "EMBED" && el.parentElement && el.parentElement.tagName === "OBJECT" ? el.parentElement : null;
    var outerParams = outer ? paramsOf(outer) : {};
    var src = el.tagName === "EMBED" ? el.getAttribute("src") : (params.movie || params.src || el.getAttribute("data"));
    if (!src) return;
    var host = document.createElement("flash-player");
    host.__flashReplaced = true;
    for (var i = 0; i < el.attributes.length; i++) {
      var at = el.attributes[i];
      try { host.setAttribute(at.name, at.value); } catch (e) { }
    }
    var st = host.style;
    st.display = "inline-block";
    st.position = "relative";
    st.width = dim(el.getAttribute("width")) || "550px";
    st.height = dim(el.getAttribute("height")) || "400px";
    st.userSelect = st.webkitUserSelect = "none";
    st.touchAction = "none";
    st.webkitTapHighlightColor = "transparent";
    st.overflow = "hidden";
    var align = (el.getAttribute("align") || "").toLowerCase();
    if (align === "left" || align === "right") st.cssFloat = align;
    el.parentNode.replaceChild(host, el);
    var url = new URL(src, document.baseURI).href;
    var bg = parseColor(params.bgcolor || outerParams.bgcolor);
    var id = (outer && outer.id) || el.getAttribute("name") || el.id || null;
    startPlayer(host, url, bg, id);
  }

  function scan(root) {
    root = root || document;
    if (root.tagName === "FLASH-PLAYER") initStatic(root);
    root.querySelectorAll("flash-player[src]").forEach(initStatic);
    // Legacy Flash markup, converted on the fly.
    root.querySelectorAll("embed, object").forEach(function (el) {
      var type = (el.getAttribute("type") || "").toLowerCase();
      var src = el.getAttribute("src") || el.getAttribute("data") || "";
      if (el.tagName === "EMBED") {
        if (type === FLASH_TYPE || /\.swf(\?|$)/i.test(src)) replace(el);
      } else {
        // <object> without an inner <embed>
        var hasEmbed = el.querySelector("embed");
        var cls = (el.getAttribute("classid") || "").toLowerCase();
        if (!hasEmbed && (type === FLASH_TYPE || cls === "clsid:d27cdb6e-ae6d-11cf-96b8-444553540000" || /\.swf(\?|$)/i.test(src))) replace(el);
      }
    });
  }

  window.FlashPlayer = { scan: scan, Player: Player };
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", function () { scan(); });
  else scan();
  // Movies inserted later by other scripts (e.g. sidebar_random.js) are
  // picked up too, as Ruffle did.
  new MutationObserver(function (muts) {
    for (var i = 0; i < muts.length; i++) {
      var added = muts[i].addedNodes;
      for (var j = 0; j < added.length; j++) {
        var n = added[j];
        if (n.nodeType !== 1) continue;
        if (n.tagName === "EMBED" || n.tagName === "OBJECT") scan(n.parentNode);
        else if (n.tagName === "FLASH-PLAYER" || n.querySelector("flash-player, embed, object")) scan(n);
      }
    }
  }).observe(document.documentElement, { childList: true, subtree: true });
})();
