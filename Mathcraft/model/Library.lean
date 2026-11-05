import «Mathcraft».model.World
import Mathlib.Control.Traversable.Basic

namespace Mathcraft

namespace Library

/--
Directory in which we save all worlds
-/
def directory : IO System.FilePath := IO.currentDir <&> (· / "worlds")

def createLibrary : IO Bool := do
  -- create the worlds directory if it doesn't exist
  let dir <- directory
  if !(← System.FilePath.pathExists dir) then
    IO.FS.createDir dir
    return true
  else
    return false

def loadWorld (folder : System.FilePath) : IO World := return {directory := folder}

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
    _ <- createLibrary
    return []

/--
The worlds stored in `dir`: one for each of its immediate subfolders, sorted by folder name.
Fails if `dir` is not a folder.
-/
def listWorldsIn (dir : System.FilePath) : IO (Array World) := do
  if !(← dir.isDir) then
    throw <| IO.userError s!"Folder not found: {dir}"
  let entries ← dir.readDir
  let folders ← entries.filterM (·.path.isDir)
  let sorted := folders.qsort (·.fileName < ·.fileName)
  sorted.mapM (loadWorld ·.path)

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
