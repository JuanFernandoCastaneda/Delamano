import Game.Levels.Equivalencias
import Game.Levels.Inferencias

-- Here's what we'll put on the title screen
Title "Equivalencias e Inferencias"
Introduction
"
Este asistente te puede ayudar a resolver ejercicios de FMC por tu cuenta, sobre todo verificando que lo que estás haciendo está bien.

En la mitad de la pantalla encontrarás \"Mundos\". Dale clic a las bolitas verdes que aparecen. Esas te llevarán a la introducción del mundo, y eventualmente a los ejercicios.

Los dos mundos de este juego son Equivalencias e Inferencias.
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
