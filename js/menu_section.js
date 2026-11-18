// FSCommand handler for menu_rus. The menu movie sends "init" when it starts;
// the page answers by jumping it to the frame that highlights the current
// section (frame 1 = news ... frame 8 = x-ray), picked from the page name.
(function () {
  var FRAMES = { news: 1, game: 2, community: 3, gallery: 4, downloads: 5, press: 6, support: 7, engine: 8 };

  function section() {
    var page = location.pathname.split("/").pop().toLowerCase();
    var m = /^index_t_([a-z0-9]+)/.exec(page);
    return m && FRAMES[m[1]] ? FRAMES[m[1]] : FRAMES.news;
  }

  window.menu_DoFSCommand = function (command) {
    if (command !== "init") return;
    var el = document.getElementById("menu");
    if (el && el.querySelector) el = el.querySelector("flash-player") || el;
    if (el && el.GotoFrame) el.GotoFrame(section());
  };
})();
