import Raylib
import Raygui
import «Mathcraft».components.raylib.Settings
import «Mathcraft».model.Library

namespace Mathcraft

namespace UI

def rowHeight : UInt32 := 40
def rowGap : UInt32 := 10
def margin : UInt32 := 20
def columnWidth : UInt32 := 670
def sideButtonWidth : UInt32 := 100
/-- Maximum length in bytes of the path in the text field. -/
def pathCapacity : UInt32 := 1024

/-- How many world buttons fit above the "New world" and path rows. -/
def maxVisibleRows : Nat :=
  ((windowHeight - 2 * margin - 2 * rowHeight - rowGap) / (rowHeight + rowGap)).toNat

def rect (x y w h : UInt32) : Raylib.Rectangle :=
  { x := x.toFloat32, y := y.toFloat32, width := w.toFloat32, height := h.toFloat32 }

/-- The screen listing the worlds of a library. -/
structure HomeScreen where
  path : String
  /-- Whether the text field has keyboard focus. -/
  editing : Bool := false
  worlds : Array World := #[]
  /-- Index of the first visible world. -/
  scroll : Nat := 0
  /-- Message shown instead of the world list after a failed load. -/
  error : Option String := none
  /-- The message to show if the load in progress fails. -/
  failure : String := "Could not load this folder"
  /-- The load in progress. Starting another one replaces it. -/
  loading : Option (Task (Except IO.Error (Array World))) := none

namespace HomeScreen

/-- Empties the list and runs `action` in the background to fill it again. -/
def startLoading (s : HomeScreen) (action : IO (Array World))
    (failure := "Could not load this folder") : BaseIO HomeScreen := do
  let task ← IO.asTask action
  return { s with worlds := #[], scroll := 0, error := none, failure, loading := some task }

/-- Loads the worlds of `s.path`. -/
def load (s : HomeScreen) : BaseIO HomeScreen :=
  s.startLoading (Library.listWorldsIn s.path)

/-- Creates a world in `s.path` and loads the worlds again. -/
def newWorld (s : HomeScreen) : BaseIO HomeScreen :=
  s.startLoading do
    let _ ← Library.newWorldIn s.path
    Library.listWorldsIn s.path

/-- Deletes `world` and loads the worlds again. -/
def deleteWorld (s : HomeScreen) (world : World) : BaseIO HomeScreen :=
  s.startLoading (failure := "Could not delete this world") do
    Library.deleteWorld world
    Library.listWorldsIn s.path

/-- The home screen for the library in `<cwd>/library`. -/
def start : IO HomeScreen := do
  let path := (← IO.currentDir) / "library"
  load { path := path.toString }

/-- Picks up the result of the load in progress, if it has finished. -/
def poll (s : HomeScreen) : IO HomeScreen := do
  let some task := s.loading | return s
  if !(← IO.hasFinished task) then
    return s
  match task.get with
  | .ok worlds => return { s with worlds, loading := none }
  | .error e =>
    IO.eprintln e
    return { s with error := some s.failure, loading := none }

def applyWheel (s : HomeScreen) (wheel : Pod.Float32) : HomeScreen :=
  let maxScroll := s.worlds.size - maxVisibleRows
  if wheel.toFloat > 0 then { s with scroll := s.scroll - 1 }
  else if wheel.toFloat < 0 then { s with scroll := min (s.scroll + 1) maxScroll }
  else s

/-- What to show in place of the world list when there are no worlds. -/
def message? (s : HomeScreen) : Option String :=
  if s.loading.isSome then some "Loading..."
  else if let some e := s.error then some e
  else if s.worlds.isEmpty then some "No worlds found"
  else none

/--
Draws one frame. Returns the state changed by the user's input,
and the world the user clicked on, if any.
-/
def draw (s : HomeScreen) : IO (HomeScreen × Option World) := do
  let visibleRows := min s.worlds.size maxVisibleRows
  let listRows := if s.worlds.isEmpty then 1 else visibleRows
  let step := rowHeight + rowGap
  let columnHeight := (listRows.toUInt32 + 1) * step + rowHeight
  let left := (windowWidth - columnWidth) / 2
  let top := (windowHeight - columnHeight) / 2

  if let some message := s.message? then
    Raygui.label (rect left top columnWidth rowHeight) message
  let sideX := left + columnWidth - sideButtonWidth
  let mainWidth := columnWidth - sideButtonWidth - rowGap
  let mut clicked : Option World := none
  let mut deleted : Option World := none
  for i in [0:visibleRows] do
    let world := s.worlds[s.scroll + i]!
    let y := top + i.toUInt32 * step
    if ← Raygui.button (rect left y mainWidth rowHeight) (← world.name) then
      clicked := some world
    if ← Raygui.button (rect sideX y sideButtonWidth rowHeight) "Delete" then
      deleted := some world

  let newWorldY := top + listRows.toUInt32 * step
  let newWorldClicked ← Raygui.button (rect left newWorldY columnWidth rowHeight) "New world"

  let pathY := newWorldY + step
  let pathBounds := rect left pathY mainWidth rowHeight
  let (toggled, path) ← Raygui.textBox pathBounds s.path pathCapacity s.editing
  let s := { s with path, editing := s.editing != toggled }

  let loadClicked ← Raygui.button (rect sideX pathY sideButtonWidth rowHeight) "Load"
  if let some world := deleted then return (← s.deleteWorld world, none)
  if loadClicked then return (← s.load, none)
  if newWorldClicked && s.loading.isNone then return (← s.newWorld, none)
  return (s, clicked)

/-- Handles input and draws one frame. See `draw` for the result. -/
def frame (s : HomeScreen) : IO (HomeScreen × Option World) := do
  let s ← s.poll
  let s := s.applyWheel (← Raylib.getMouseWheelMove)
  s.draw

end HomeScreen

end UI

end Mathcraft
