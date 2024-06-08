import «Mathcraft».model.Block
import Mathlib.Data.Fin.Basic

namespace Mathcraft

abbrev Chunk.AxisLocation : Type := Int
abbrev Chunk.Width : Nat := 32
abbrev Chunk.Height : Nat := 256
abbrev Chunk.Depth : Nat := 32

structure Chunk where
  x : Chunk.AxisLocation
  y : Chunk.AxisLocation
  data : Array Block
  hSize: data.size = Chunk.Width * Chunk.Height * Chunk.Depth

def Chunk.PositionToInt
  (x : Fin Chunk.Width)
  (y : Fin Chunk.Height)
  (z : Fin Chunk.Depth)
  : Fin (Chunk.Width * Chunk.Height * Chunk.Depth) :=
  let val := y * Chunk.Width * Chunk.Depth + z * Chunk.Width + x
  ⟨
    val,
    by
      -- subtract both sides by `Chunk.Width * Chunk.Height * Chunk.Depth`
      simp only [Nat.cast_ofNat]
      sorry
  ⟩

def Chunk.IntToPosition
  (i : Fin (Chunk.Width * Chunk.Height * Chunk.Depth))
  : Fin Chunk.Width × Fin Chunk.Height × Fin Chunk.Depth:= (
    sorry,
    sorry,
    sorry
  )



def Chunk.getBlock
  (x : Fin Chunk.Width)
  (y : Fin Chunk.Height)
  (z : Fin Chunk.Depth)
  (c : Chunk) : Block :=
  c.data.get! $ y * Chunk.Width * Chunk.Depth + z * Chunk.Width + x

def Chunk.empty (x y : Chunk.AxisLocation) : Chunk := {
    x := x,
    y := y,
    data := Array.mkArray (Chunk.Width * Chunk.Height * Chunk.Depth) 0,
    hSize := by
      unfold Array.size
      unfold Array.mkArray
      sorry
  }

def Chunk.read (x y: Chunk.AxisLocation) (bytes : ByteArray) : Chunk := Id.run do
  let mut data : Array Block := Array.empty
  for y' in [0:Chunk.Height] do
    let mut row : Array (Array (UInt8)) := Array.empty
    for z' in [0:Chunk.Depth] do
      let mut column : Array (UInt8) := Array.empty
      for x' in [0:Chunk.Width] do
        data := data.push (bytes.get! (x' * Chunk.Height * Chunk.Depth + y' * Chunk.Depth + z'))
  return {
    x := x,
    y := y,
    data := data,
    hSize := by
      unfold Array.size
      sorry
  }

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

/--
The filename of a saved chunk encodes the location of said chunk.
Givne the filename, we can extract the location of the chunk.
-/
def Chunk.axisLocationFromFilename (filename : String) : Option (Chunk.AxisLocation × Chunk.AxisLocation) :=
  let parts := filename.splitOn "_"
  if parts.length = 3 then
    let x := parts.get! 1
    let y := parts.get! 2
    let x' := x.toInt?
    let y' := y.toInt?
    if x'.isSome && y'.isSome then
      some (x'.get!, y'.get!)
    else
      none
  else
    none

/--
Read a chunk from a file path
-/
def Chunk.readFromFile (file : System.FilePath) : IO (Option Chunk) := do
  let ex ← System.FilePath.pathExists file
  if ex then
    let bytes ← IO.FS.readBinFile file
    let p := file.fileName  >>= Chunk.axisLocationFromFilename
    if p.isSome then
      let ⟨x,y⟩ := p.get!
      return Chunk.read x y bytes
    else
      return none
  else
    return none

end Mathcraft
