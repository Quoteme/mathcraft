import «Mathcraft».model.Chunk

namespace Mathcraft

/-- The position of a block: the chunk it is in, and where it is inside that chunk. -/
structure BlockPosition where
  chunk : Chunk.Coord
  x : Fin Chunk.Width
  y : Fin Chunk.Height
  z : Fin Chunk.Depth
  deriving DecidableEq, Repr

/-- Something that lives in a chunk but is not a block, like a player or a zombie. -/
structure Entity where
  /-- Identifies the entity, whichever chunk it moves to. -/
  id : Nat
  kind : Nat
  /-- The block the entity is in. This determines its chunk. -/
  block : BlockPosition
  /-- The position inside that block, each coordinate in `[0, 1)`. -/
  offset : Float × Float × Float
  deriving Repr

def Entity.chunk (e : Entity) : Chunk.Coord := e.block.chunk

/-- The same entity, moved to another block. -/
def Entity.moveTo (e : Entity) (block : BlockPosition) : Entity := { e with block }

end Mathcraft
