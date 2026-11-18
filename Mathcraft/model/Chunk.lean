import «Mathcraft».model.Block
import Mathlib.Data.Fin.Basic

namespace Mathcraft

abbrev Chunk.Width : Nat := 32
abbrev Chunk.Height : Nat := 256
abbrev Chunk.Depth : Nat := 32

/-- A box of blocks. `data` gives the block at every position inside the box. -/
structure Chunk where
  id : Int
  width : Nat
  height : Nat
  depth : Nat
  data : Fin width × Fin height × Fin depth → Block

def Chunk.getBlock (c : Chunk) (x : Fin c.width) (y : Fin c.height) (z : Fin c.depth) : Block :=
  c.data (x, y, z)

def Chunk.empty (id : Int) (width height depth : Nat) : Chunk :=
  { id, width, height, depth, data := fun _ ↦ Block.air }

/-- A chunk filled with grass up to `grassHeight`. -/
def Chunk.flat (id : Int) (width height depth grassHeight : Nat) : Chunk :=
  { id, width, height, depth,
    data := fun ⟨_, y, _⟩ ↦ if y.val < grassHeight then Block.grass else Block.air }

/-- Reads the blocks of a chunk, stored x-major: `x * height * depth + y * depth + z`. -/
def Chunk.read (id : Int) (width height depth : Nat) (bytes : ByteArray) : Chunk :=
  { id, width, height, depth,
    data := fun ⟨x, y, z⟩ ↦ bytes.get! (x.val * height * depth + y.val * depth + z.val) }

/-- Writes the blocks of a chunk in the layout `Chunk.read` expects. -/
def Chunk.write (c : Chunk) : ByteArray := Id.run do
  let mut bytes : ByteArray := ByteArray.empty
  for hi : i in [0:c.width] do
    for hj : j in [0:c.height] do
      for hk : k in [0:c.depth] do
        bytes := bytes.push $ c.getBlock ⟨i, hi.2⟩ ⟨j, hj.2⟩ ⟨k, hk.2⟩
  return bytes

/-- Reads the chunk with the given id and dimensions from a file. -/
def Chunk.readFromFile (id : Int) (width height depth : Nat) (file : System.FilePath) :
    IO (Option Chunk) := do
  if ← System.FilePath.pathExists file then
    let bytes ← IO.FS.readBinFile file
    if bytes.size == width * height * depth then
      return Chunk.read id width height depth bytes
  return none

end Mathcraft
