import Raylib

namespace Mathcraft

namespace UI

namespace Window

def width : UInt32 := 800
def height : UInt32 := 600
def title : String := "Mathcraft"
def targetFPS : UInt32 := 60

/-- Opens the game window and keeps it open until the user closes it. -/
def main : IO Unit := do
  let ctx ← Raylib.initWindow width height title.toSubstring
  Raylib.setTargetFPS targetFPS
  repeat
    Raylib.beginDrawing
    Raylib.clearBackground Raylib.raywhite
    Raylib.endDrawing
    if (← Raylib.windowShouldClose) then break
  Raylib.closeWindow ctx

end Window

end UI

end Mathcraft
