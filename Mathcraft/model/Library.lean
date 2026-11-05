import «Mathcraft».model.World
import Mathlib.Control.Traversable.Basic

namespace Mathcraft

namespace Library

/--
Directory in which we save all worlds
-/
def directory : IO System.FilePath := IO.currentDir <&> (· / "worlds")

/--
Creates the library folder `dir` and any missing parent folders.
Returns whether the folder had to be created.
-/
def createLibrary (dir : System.FilePath) : IO Bool := do
  if !(← System.FilePath.pathExists dir) then
    IO.FS.createDirAll dir
    return true
  else
    return false

def loadWorld (folder : System.FilePath) : IO World := return {
  directory := folder
}

def loadWorldByName (name : String) : IO (Option World) := do
  let dir <- directory
  let path := dir / name
  if (← System.FilePath.pathExists path) then
    return some (← loadWorld path)
  else
    return none

def listWorlds : IO (List World) := do
  -- list all the directories in the current directory
  let dir <- directory
  if (← System.FilePath.pathExists dir) then
    let folders <- System.FilePath.walkDir dir (λ _ ↦ return true)
    let w := folders.data.map loadWorld
    sequence w
  else
    _ <- createLibrary dir
    return []

/--
The worlds stored in `dir`: one for each of its immediate subfolders, sorted by folder name.
Creates `dir` if it doesn't exist. Fails if `dir` is not a folder.
-/
def listWorldsIn (dir : System.FilePath) : IO (Array World) := do
  _ <- createLibrary dir
  if !(← dir.isDir) then
    throw <| IO.userError s!"Folder not found: {dir}"
  let entries ← dir.readDir
  let folders ← entries.filterM (·.path.isDir)
  let sorted := folders.qsort (·.fileName < ·.fileName)
  sorted.mapM (loadWorld ·.path)

/--
Creates a world in `dir` named after the first free number: `World 1`, `World 2`, ...
It starts out with four flat chunks around the origin.
-/
def newWorldIn (dir : System.FilePath) : IO World := do
  _ <- createLibrary dir
  let mut n := 1
  while ← (dir / s!"World {n}").pathExists do
    n := n + 1
  let path := dir / s!"World {n}"
  IO.FS.createDir path
  let world ← loadWorld path
  for (x, y) in [((-1 : Chunk.AxisLocation), (-1 : Chunk.AxisLocation)), (-1, 0), (0, -1), (0, 0)] do
    world.saveChunk (Chunk.flat x y 4)
  return world

/--
Deletes the folder of a world. Fails without deleting anything if the folder holds anything but
chunk files, as a library can list any folder as a world.
-/
def deleteWorld (w : World) : IO Unit := do
  let entries ← w.directory.readDir
  let isChunkFile (name : String) : Bool :=
    match Chunk.axisLocationFromFilename name with
    | some (x, y) => name == Chunk.filename x y
    | none => false
  if !entries.all (isChunkFile ·.fileName) then
    throw <| IO.userError s!"Not a world, it holds other files: {w.directory}"
  for entry in entries do
    IO.FS.removeFile entry.path
  IO.FS.removeDir w.directory

def saveWorld (w : World) : IO Unit := do
  let dir <- directory
  let path := dir / w.directory
  if !(← System.FilePath.pathExists path) then
    IO.FS.createDir path
  return ()

def newWorld (name : String) : IO World := do
  let dir <- directory
  let path := dir / name
  if !(← System.FilePath.pathExists path) then
    IO.FS.createDir path
  return {directory := name}

end Library

end Mathcraft
