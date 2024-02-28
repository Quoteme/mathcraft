import «Mathcraft».World
import Mathlib.Control.Traversable.Basic

namespace Mathcraft

namespace Library

/--
The WorldLoader is responsible for loading and saving worlds.

It is an abstraction around
-/
def directory : IO System.FilePath := IO.currentDir <&> (· / "worlds")

def createLibrary : IO Unit := do
  -- create the worlds directory if it doesn't exist
  let dir <- directory
  if !(← System.FilePath.pathExists dir) then
    IO.FS.createDir dir
  return ()

def loadWorld (folder : System.FilePath) : IO World := return {directory := folder}

def listWorlds : IO (List World) := do
  -- list all the directories in the current directory
  let dir <- directory
  if (← System.FilePath.pathExists dir) then
    let folders <- System.FilePath.walkDir dir (λ _ ↦ return true)
    let w := folders.data.map loadWorld
    sequence w
  else
    createLibrary
    return []

end Library

end Mathcraft
