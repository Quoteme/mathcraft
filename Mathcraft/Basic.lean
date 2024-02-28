import Init.Prelude
import Lean.Data.Json.Parser
import Mathlib.Control.Traversable.Basic

namespace Mathcraft

abbrev Block := UInt8
abbrev Chunk.AxisLocation : Type := Int
abbrev Chunk.Width : Nat := 32
abbrev Chunk.Height : Nat := 256
abbrev Chunk.Depth : Nat := 32
abbrev Chunk.BlockArray : Type := Array (Array (Array (Block)))

structure Chunk where
  x : Chunk.AxisLocation
  y : Chunk.AxisLocation
  data : Chunk.BlockArray
  hHeight: Prop := data.size = Chunk.Width
  hWidth: Prop := data.all (λ row => row.size = Chunk.Height)
  hDepth: Prop := data.all (λ row => row.all (λ column => column.size = Chunk.Depth))

def Chunk.getBlock
  (x : Fin Chunk.Width)
  (y : Fin Chunk.Height)
  (z : Fin Chunk.Depth)
  (c : Chunk) : Block :=
  let slice := c.data.get! x
  let row := slice.get! y
  let block := row.get! z
  block

def Chunk.empty : Chunk :=
  Chunk.mk
    (x := 0)
    (y := 0)
    (data := Array.mkArray Chunk.Width (Array.mkArray Chunk.Height (Array.mkArray Chunk.Depth 0)))
    (hHeight := sorry)
    (hWidth := sorry)
    (hDepth := sorry)

def Chunk.read (x y: Chunk.AxisLocation) (bytes : ByteArray) : Chunk := Id.run do
  let mut data : Chunk.BlockArray := Array.empty
  for i in [0:Chunk.Width] do
    let mut row : Array (Array (UInt8)) := Array.empty
    for j in [0:Chunk.Height] do
      let mut column : Array (UInt8) := Array.empty
      for k in [0:Chunk.Depth] do
        column := column.push (bytes.get! (i * Chunk.Height * Chunk.Depth + j * Chunk.Depth + k))
      row := row.push column
    data := data.push row
  return Chunk.mk
    (x := x)
    (y := y)
    (data := data)
    (hHeight := sorry)
    (hWidth := sorry)
    (hDepth := sorry)

def Chunk.write (c : Chunk) : ByteArray := Id.run do
  let mut bytes : ByteArray := ByteArray.empty
  for i in [0:Chunk.Width] do
    for j in [0:Chunk.Height] do
      for k in [0:Chunk.Depth] do
        let i' : Fin Chunk.Width := ⟨i, by sorry⟩
        let j' : Fin Chunk.Height := ⟨j, by sorry⟩
        let k' : Fin Chunk.Depth := ⟨k, by sorry⟩
        bytes := bytes.push $ c.getBlock i' j' k'
  return bytes

def Chunk.filename (x y : Chunk.AxisLocation) : String :=
  s!"chunk_{x}_{y}.bin"

structure World where
  directory : System.FilePath
  deriving Inhabited, Repr

def World.chunkExists (x y : Chunk.AxisLocation) (w : World) : IO Bool := do
  -- check if the file `{directory}/chunk_{x}_{y}.bin` exists
  let filename : String := Chunk.filename x y
  let filepath : System.FilePath := System.FilePath.withFileName (directory w) filename
  System.FilePath.pathExists filepath

def World.getChunk (x y : Chunk.AxisLocation) (w : World) : IO (Option Chunk) := do
  -- read in the file `{directory}/chunk_{x}_{y}.bin`
  let fileName : String := Chunk.filename x y
  let filePath : System.FilePath := System.FilePath.withFileName (directory w) fileName
  let fileExists : Bool ← System.FilePath.pathExists filePath
  if !fileExists then
    return none
  else do
    let bytes : ByteArray ← IO.FS.readBinFile filePath
    let chunk : Chunk := Chunk.read x y bytes
    return some chunk

def World.saveChunk (c : Chunk) (w : World) : IO Unit := do
  -- write the chunk to the file `{directory}/chunk_{c.x}_{c.y}.bin`
  let fileName : String := s!"chunk_{c.x}_{c.y}.bin"
  let filePath : System.FilePath := System.FilePath.withFileName (directory w) fileName
  let bytes : ByteArray := Chunk.write c
  IO.FS.writeBinFile filePath bytes

def World.createChunk (x y : Chunk.AxisLocation) (w : World) : IO Chunk := do
  -- create a new chunk with the given x and y coordinates
  let c : Chunk := Chunk.empty
  World.saveChunk c w
  return c

def World.getOrCreateChunk (x y : Chunk.AxisLocation) (w : World) : IO Chunk := do
  -- check if the chunk exists
  let c : Option Chunk ← World.getChunk x y w
    match c with
    | some c => return c
    | none => return (← World.createChunk x y w)

/--
The WorldLoader is responsible for loading and saving worlds.

It is an abstraction around
-/
def WorldLoader.directory : IO System.FilePath := IO.currentDir <&> (· / "worlds")

def WorldLoader.createLibrary : IO Unit := do
  -- create the worlds directory if it doesn't exist
  let dir <- WorldLoader.directory
  if !(← System.FilePath.pathExists dir) then
    IO.FS.createDir dir
  return ()

def WorldLoader.loadWorld (folder : System.FilePath) : IO World := return {directory := folder}

def WorldLoader.listWorlds : IO (List World) := do
  -- list all the directories in the current directory
  let dir <- WorldLoader.directory
  if (← System.FilePath.pathExists dir) then
    let folders <- System.FilePath.walkDir dir (λ _ ↦ return true)
    let w := folders.data.map WorldLoader.loadWorld
    sequence w
  else
    WorldLoader.createLibrary
    return []

end Mathcraft
