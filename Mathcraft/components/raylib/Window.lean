import Raylib
import Raygui
import «Mathcraft».model.Library

namespace Mathcraft

namespace UI

namespace Window

def width : UInt32 := 800
def height : UInt32 := 600
def title : String := "Mathcraft"
def targetFPS : UInt32 := 60

def fontSize : UInt32 := 20
def rowHeight : UInt32 := 40
def rowGap : UInt32 := 10
def margin : UInt32 := 20
def columnWidth : UInt32 := 670
def loadButtonWidth : UInt32 := 100
/-- Maximum length in bytes of the path in the text field. -/
def pathCapacity : UInt32 := 1024

/-- How many world buttons fit above the "New world" and path rows. -/
def maxVisibleRows : Nat :=
  ((height - 2 * margin - 2 * rowHeight - rowGap) / (rowHeight + rowGap)).toNat

structure State where
  path : String
  /-- Whether the text field has keyboard focus. -/
  editing : Bool := false
  worlds : Array World := #[]
  /-- Index of the first visible world. -/
  scroll : Nat := 0
  /-- Message shown instead of the world list after a failed load. -/
  error : Option String := none
  /-- The load in progress. Starting another one replaces it. -/
  loading : Option (Task (Except IO.Error (Array World))) := none

/-- Empties the list and runs `action` in the background to fill it again. -/
def State.startLoading (s : State) (action : IO (Array World)) : BaseIO State := do
  let task ← IO.asTask action
  return { s with worlds := #[], scroll := 0, error := none, loading := some task }

/-- Loads the worlds of `s.path`. -/
def State.load (s : State) : BaseIO State :=
  s.startLoading (Library.listWorldsIn s.path)

/-- Creates a world in `s.path` and loads the worlds again. -/
def State.newWorld (s : State) : BaseIO State :=
  s.startLoading do
    let _ ← Library.newWorldIn s.path
    Library.listWorldsIn s.path

/-- Picks up the result of the load in progress, if it has finished. -/
def State.poll (s : State) : IO State := do
  let some task := s.loading | return s
  if !(← IO.hasFinished task) then
    return s
  match task.get with
  | .ok worlds => return { s with worlds, loading := none }
  | .error e =>
    IO.eprintln e
    return { s with error := some "Could not load this folder", loading := none }

def State.applyWheel (s : State) (wheel : Pod.Float32) : State :=
  let maxScroll := s.worlds.size - maxVisibleRows
  if wheel.toFloat > 0 then { s with scroll := s.scroll - 1 }
  else if wheel.toFloat < 0 then { s with scroll := min (s.scroll + 1) maxScroll }
  else s

/-- What to show in place of the world list when there are no worlds. -/
def State.message? (s : State) : Option String :=
  if s.loading.isSome then some "Loading..."
  else if let some e := s.error then some e
  else if s.worlds.isEmpty then some "No worlds found"
  else none

def rect (x y w h : UInt32) : Raylib.Rectangle :=
  { x := x.toFloat32, y := y.toFloat32, width := w.toFloat32, height := h.toFloat32 }

/-- Draws one frame of the column and returns the state changed by the user's input. -/
def State.draw (s : State) : IO State := do
  let visibleRows := min s.worlds.size maxVisibleRows
  let listRows := if s.worlds.isEmpty then 1 else visibleRows
  let step := rowHeight + rowGap
  let columnHeight := (listRows.toUInt32 + 1) * step + rowHeight
  let left := (width - columnWidth) / 2
  let top := (height - columnHeight) / 2

  if let some message := s.message? then
    Raygui.label (rect left top columnWidth rowHeight) message
  for i in [0:visibleRows] do
    let name ← s.worlds[s.scroll + i]!.name
    let y := top + i.toUInt32 * step
    let _ ← Raygui.button (rect left y columnWidth rowHeight) name

  let newWorldY := top + listRows.toUInt32 * step
  let newWorldClicked ← Raygui.button (rect left newWorldY columnWidth rowHeight) "New world"

  let pathY := newWorldY + step
  let pathBounds := rect left pathY (columnWidth - loadButtonWidth - rowGap) rowHeight
  let (toggled, path) ← Raygui.textBox pathBounds s.path pathCapacity s.editing
  let s := { s with path, editing := s.editing != toggled }

  let loadX := left + columnWidth - loadButtonWidth
  let loadClicked ← Raygui.button (rect loadX pathY loadButtonWidth rowHeight) "Load"
  if loadClicked then s.load
  else if newWorldClicked && s.loading.isNone then s.newWorld
  else return s

/-- Opens the game window and keeps it open until the user closes it. -/
def main : IO Unit := do
  let ctx ← Raylib.initWindow width height title.toSubstring
  Raylib.setTargetFPS targetFPS
  Raygui.setStyle .default Raygui.DefaultProperty.textSize fontSize
  Raygui.setStyle .label Raygui.ControlProperty.textAlignment Raygui.TextAlignment.center.val

  let path := (← IO.currentDir) / "library"
  let mut state ← State.load { path := path.toString }
  repeat
    state ← state.poll
    state := state.applyWheel (← Raylib.getMouseWheelMove)
    Raylib.beginDrawing
    Raylib.clearBackground .raywhite
    state ← state.draw
    Raylib.endDrawing
    if (← Raylib.windowShouldClose) then break
  Raylib.closeWindow ctx

end Window

end UI

end Mathcraft
