import «Mathcraft».model.Block
import Mathlib.Data.Fin.Basic
import Std.Tactic.Omega

namespace Mathcraft

abbrev Chunk.AxisLocation : Type := Int
abbrev Chunk.Width : Nat := 32
abbrev Chunk.Height : Nat := 256
abbrev Chunk.Depth : Nat := 32

/-- The location of a chunk in the world. -/
abbrev Chunk.Coord : Type := Chunk.AxisLocation × Chunk.AxisLocation

/-- The position of a block: the chunk it is in, and where it is inside that chunk. -/
structure BlockPosition where
  chunk : Chunk.Coord
  x : Fin Chunk.Width
  y : Fin Chunk.Height
  z : Fin Chunk.Depth
  deriving DecidableEq, Repr

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
  ⟨
    y.val * Chunk.Width * Chunk.Depth + z.val * Chunk.Width + x.val,
    by
      have hx : x.val < 32 := x.isLt
      have hy : y.val < 256 := y.isLt
      have hz : z.val < 32 := z.isLt
      show y.val * 32 * 32 + z.val * 32 + x.val < 32 * 256 * 32
      omega
  ⟩

def Chunk.IntToPosition
  (i : Fin (Chunk.Width * Chunk.Height * Chunk.Depth))
  : Fin Chunk.Width × Fin Chunk.Height × Fin Chunk.Depth :=
  have hi : i.val < 32 * 256 * 32 := i.isLt
  (
    ⟨i.val % Chunk.Width, by show i.val % 32 < 32; omega⟩,
    ⟨i.val / (Chunk.Width * Chunk.Depth), by show i.val / 1024 < 256; omega⟩,
    ⟨i.val / Chunk.Width % Chunk.Depth, by show i.val / 32 % 32 < 32; omega⟩
  )

theorem Chunk.positionToInt_intToPosition
  (i : Fin (Chunk.Width * Chunk.Height * Chunk.Depth)) :
  let (x, y, z) := Chunk.IntToPosition i
  Chunk.PositionToInt x y z = i := by
  apply Fin.ext
  show i.val / 1024 * 32 * 32 + i.val / 32 % 32 * 32 + i.val % 32 = i.val
  omega

theorem Chunk.intToPosition_positionToInt
  (x : Fin Chunk.Width)
  (y : Fin Chunk.Height)
  (z : Fin Chunk.Depth) :
  Chunk.IntToPosition (Chunk.PositionToInt x y z) = (x, y, z) := by
  have hx : x.val < 32 := x.isLt
  have hz : z.val < 32 := z.isLt
  refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
  · show (y.val * 32 * 32 + z.val * 32 + x.val) % 32 = x.val
    omega
  · show (y.val * 32 * 32 + z.val * 32 + x.val) / 1024 = y.val
    omega
  · show (y.val * 32 * 32 + z.val * 32 + x.val) / 32 % 32 = z.val
    have h : (y.val * 32 * 32 + z.val * 32 + x.val) / 32 = y.val * 32 + z.val := by omega
    rw [h]
    omega

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
    hSize := Array.size_mkArray _ _
  }

/-- A chunk filled with grass up to `grassHeight`. -/
def Chunk.flat (x y : Chunk.AxisLocation) (grassHeight : Nat) : Chunk := {
    x := x,
    y := y,
    data := Array.ofFn fun (i : Fin (Chunk.Width * Chunk.Height * Chunk.Depth)) ↦
      if i.val < grassHeight * Chunk.Width * Chunk.Depth then Block.grass else Block.air,
    hSize := Array.size_ofFn _
  }

def Chunk.read (x y: Chunk.AxisLocation) (bytes : ByteArray) : Chunk := {
    x := x,
    y := y,
    data := Array.ofFn fun i ↦
      let (x', y', z') := Chunk.IntToPosition i
      bytes.get! (x'.val * Chunk.Height * Chunk.Depth + y'.val * Chunk.Depth + z'.val),
    hSize := Array.size_ofFn _
  }

def Chunk.write (c : Chunk) : ByteArray := Id.run do
  let mut bytes : ByteArray := ByteArray.empty
  for hi : i in [0:Chunk.Width] do
    for hj : j in [0:Chunk.Height] do
      for hk : k in [0:Chunk.Depth] do
        let i' : Fin Chunk.Width := ⟨i, hi.2⟩
        let j' : Fin Chunk.Height := ⟨j, hj.2⟩
        let k' : Fin Chunk.Depth := ⟨k, hk.2⟩
        bytes := bytes.push $ c.getBlock i' j' k'
  return bytes

def Chunk.filename (x y : Chunk.AxisLocation) : String :=
  s!"chunk_{x}_{y}.bin"

/--
The filename of a saved chunk encodes the location of said chunk.
Givne the filename, we can extract the location of the chunk.
-/
def Chunk.axisLocationFromFilename (filename : String) : Option (Chunk.AxisLocation × Chunk.AxisLocation) :=
  let stem := (filename : System.FilePath).fileStem.getD filename
  let parts := stem.splitOn "_"
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
    if p.isSome && bytes.size == Chunk.Width * Chunk.Height * Chunk.Depth then
      let ⟨x,y⟩ := p.get!
      return Chunk.read x y bytes
    else
      return none
  else
    return none

end Mathcraft
