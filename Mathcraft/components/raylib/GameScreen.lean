import Raylib
import Raygui
import «Mathcraft».components.raylib.HomeScreen
import «Mathcraft».model.World

open Raylib (Color)
open Raymath (Vector3)

namespace Mathcraft

namespace UI

/-- A block that gets drawn. -/
structure Voxel where
  position : Vector3
  color : Color

/-- Slightly different colors make neighbouring blocks of the same type distinguishable. -/
def blockColor (block : Block) (x z : Nat) : Color :=
  let shade : UInt8 := if (x + z) % 2 == 0 then 0 else 20
  if block == Block.grass then Color.fromRgba (70 + shade) (150 + shade) 60 255
  else if block == Block.water then Color.fromRgba 50 (90 + shade) 200 255
  else Color.fromRgba (120 + shade) (120 + shade) (120 + shade) 255

/-- The blocks of `c` that could be visible: those next to air or at the edge of the chunk. -/
def voxelsOf (c : Chunk) : Array Voxel := Id.run do
  let layer := Chunk.Width * Chunk.Depth
  let originX := c.x * Chunk.Width
  let originZ := c.y * Chunk.Depth
  let isAir (i : Nat) : Bool := c.data[i]! == Block.air
  let mut voxels := #[]
  for i in [0:c.data.size] do
    let block := c.data[i]!
    if block != Block.air then
      let x := i % Chunk.Width
      let z := (i / Chunk.Width) % Chunk.Depth
      let y := i / layer
      let exposed :=
        x == 0 || x + 1 == Chunk.Width || z == 0 || z + 1 == Chunk.Depth ||
        y == 0 || y + 1 == Chunk.Height ||
        isAir (i - 1) || isAir (i + 1) ||
        isAir (i - Chunk.Width) || isAir (i + Chunk.Width) ||
        isAir (i - layer) || isAir (i + layer)
      if exposed then
        let toFloat32 (v : Int) := (Float.ofInt v).toFloat32
        let position := Vector3.mk
          (toFloat32 (originX + x)) (toFloat32 y) (toFloat32 (originZ + z))
        voxels := voxels.push { position, color := blockColor block x z }
  return voxels

/-- The screen showing the voxels of a world. -/
structure GameScreen where
  world : World
  camera : Raylib.Camera3D
  voxels : Array Voxel := #[]
  /-- Message shown on top of the world. -/
  message : Option String := none
  /-- The world being read from disk. -/
  loading : Option (Task (Except IO.Error (Array Voxel))) := none

namespace GameScreen

/-- All the voxels of a world. -/
def loadVoxels (world : World) : IO (Array Voxel) := do
  let chunks ← world.listChunks
  return chunks.foldl (fun voxels chunk ↦ voxels ++ voxelsOf chunk) #[]

/-- Captures the mouse and starts reading `world` in the background. -/
def start (world : World) : IO GameScreen := do
  Raylib.disableCursor
  let task ← IO.asTask (loadVoxels world)
  let camera := Raylib.Camera3D.mk
    (Vector3.mk (-45) 25 (-45)) (Vector3.mk 0 0 0) (Vector3.mk 0 1 0) 60 .perspective
  return { world, camera, message := some "Loading...", loading := some task }

/-- Picks up the voxels once they have been read. -/
def poll (s : GameScreen) : IO GameScreen := do
  let some task := s.loading | return s
  if !(← IO.hasFinished task) then
    return s
  match task.get with
  | .ok voxels =>
    let message := if voxels.isEmpty then some "This world is empty" else none
    return { s with voxels, message, loading := none }
  | .error e =>
    IO.eprintln e
    return { s with message := some "Could not load this world", loading := none }

/-- Draws one frame. Returns `none` once the user leaves the world by pressing escape. -/
def frame (s : GameScreen) : IO (Option GameScreen) := do
  let s ← s.poll
  let camera ← Raylib.updateCamera s.camera .free
  let s := { s with camera }
  Raylib.beginMode3D s.camera
  for voxel in s.voxels do
    Raylib.drawCube voxel.position 1 1 1 voxel.color
  Raylib.endMode3D
  if let some message := s.message then
    Raygui.label (rect 0 (windowHeight / 2) windowWidth rowHeight) message
  Raygui.label (rect 0 margin windowWidth rowHeight) "WASD and mouse to move, Esc to leave"
  if ← Raylib.isKeyPressed .escape then
    Raylib.enableCursor
    return none
  return some s

end GameScreen

end UI

end Mathcraft
