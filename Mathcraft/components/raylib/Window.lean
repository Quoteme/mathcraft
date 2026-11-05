import Raylib
import Raygui
import «Mathcraft».components.raylib.GameScreen
import «Mathcraft».components.raylib.HomeScreen

namespace Mathcraft

namespace UI

namespace Window

def title : String := "Mathcraft"
def targetFPS : UInt32 := 60
def fontSize : UInt32 := 20

/-- Opens the game window and keeps it open until the user closes it. -/
def main : IO Unit := do
  let ctx ← Raylib.initWindow windowWidth windowHeight title.toSubstring
  Raylib.setTargetFPS targetFPS
  -- Escape leaves the game screen, it shouldn't close the window as well.
  Raylib.setExitKey .null
  Raygui.setStyle .default Raygui.DefaultProperty.textSize fontSize
  Raygui.setStyle .label Raygui.ControlProperty.textAlignment Raygui.TextAlignment.center.val

  let mut home ← HomeScreen.start
  let mut game : Option GameScreen := none
  repeat
    Raylib.beginDrawing
    Raylib.clearBackground .raywhite
    match game with
    | some screen => game ← screen.frame
    | none =>
      let (screen, opened) ← home.frame
      home := screen
      if let some world := opened then
        game := some (← GameScreen.start world)
    Raylib.endDrawing
    if (← Raylib.windowShouldClose) then break
  Raylib.closeWindow ctx

end Window

end UI

end Mathcraft
