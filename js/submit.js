function submit (url, form) {
	eval('document.' + form + '.action="' + url + '"');
	eval('document.' + form + '.submit();')
}
function reset (obj){
	eval('document.'+obj+'.value ="";');
}