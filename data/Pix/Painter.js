var counter = 0
var motion = true
var millisecs = 30
lg = images.length

function back() 
   {if (counter > 0) {counter--} else {counter = lg-1}
    showFile(counter)}
function forth() 
   {if (counter < lg-1) {counter++} else {counter = 0}
    showFile(counter)}
	
function loop(button)
   {if (button.value == "stop") {motion = false; button.value = "loop"} 
    else {motion = true; start(); button.value = "stop"}}
function start()
   {if (motion) {forth(); setTimeout("start()",millisecs)}}
   
function backStop(button) 
   {if (button.value == "stop") {motion = false; button.value = "|<<"} 
    else {motion = true; startBack(); button.value = "stop"}}
function startBack()
   {if (motion) {back2(); setTimeout("startBack()",millisecs)}}
function back2()
   {if (counter > 0) {counter--} else {button.value = "|<<"}
    showFile(counter)}
	
function forthStop(button) 
   {if (button.value == "stop") {motion = false; button.value = ">>|"} 
    else {motion = true; startForth(); button.value = "stop"}}
function startForth()
   {if (motion) {forth2(); setTimeout("startForth()",millisecs)}}
function forth2()
   {if (counter < lg-1) {counter++} else {button.value = ">>|"}
    showFile(counter)}
   
function showFile(i)
   {image = document.getElementById("img")
    slider = document.getElementById("fileSlider")
    document.getElementById("file").innerHTML = images[i]
    image.src = images[i] 
    slider.value = i
	counter = i}
		
function showTime(time)
   {document.getElementById("time").innerHTML = time
    millisecs = time}
