import «Mathcraft».Block

namespace Mathcraft

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

def Chunk.empty : Chunk := {
    x := 0,
    y := 0,
    data := Array.mkArray Chunk.Width (Array.mkArray Chunk.Height (Array.mkArray Chunk.Depth 0)),
    hHeight := sorry,
    hWidth := sorry,
    hDepth := sorry,
  }

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
  return {
    x := x,
    y := y,
    data := data,
    hHeight := sorry,
    hWidth := sorry,
    hDepth := sorry,
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
