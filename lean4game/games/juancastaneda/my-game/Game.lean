import Game.Levels.Equivalencias

-- Here's what we'll put on the title screen
Title "Asistente de pruebas FMC"
Introduction
"
Este asistente te puede ayudar a resolver ejercicios de FMC por tu cuenta, sobre todo verificando que lo que estás haciendo está bien.

En la mitad de la pantalla encontrarás \"Mundos\". Actualmente solo existe el de equivalencias, pero la idea es eventualmente agregar más, cada uno con temas nuevos.

Dale clic a las bolitas verdes que aparecen. Esas te llevarán a la introducción del mundo, y eventualmente a los ejercicios.
"

Info "

"

/-! Information to be displayed on the servers landing page. -/
Languages "Spanish"
-- CaptionShort "Equivalencias lógicas"
-- CaptionLong "Caption"
Prerequisites "Ninguno" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
