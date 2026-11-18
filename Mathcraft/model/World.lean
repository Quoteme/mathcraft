import «Mathcraft».model.Block
import «Mathcraft».model.Chunk

namespace Mathcraft

structure World where
  -- A world is just a directory where the chunks are stored as json files
  directory : System.FilePath
  deriving Inhabited, Repr

def World.name (w : World) : IO String := do
  -- get the name of the world from the directory
  return (w.directory.components.getLastD "unknown")

def World.listChunks (w : World) : IO (List Chunk) := do
  -- list all the files in the directory and read in the chunks
  let files : List System.FilePath := ( ← System.FilePath.walkDir (directory w) (λ _ ↦ return true) ).data
  let chunks : List Chunk ← files.filterMapM fun file => do
    let chunk' ← Chunk.readFromFile file
    if let some chunk := chunk' then
      return some chunk
    else
      return none
  return chunks

end Mathcraft
