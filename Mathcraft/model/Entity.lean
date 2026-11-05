import «Mathcraft».model.Chunk

namespace Mathcraft

/-- Whether `v` is a coordinate inside a chunk of the given size. This is false for NaN. -/
def Entity.InBounds (size : Nat) (v : Float) : Prop := 0 ≤ v ∧ v < size.toFloat

instance (size : Nat) (v : Float) : Decidable (Entity.InBounds size v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Something that lives in a chunk but is not a block, like a player or a zombie. -/
structure Entity where
  /-- Identifies the entity, whichever chunk it moves to. -/
  id : Nat
  kind : Nat
  chunk : Chunk.Coord
  /-- The position inside the chunk. -/
  x : Float
  y : Float
  z : Float
  hx : Entity.InBounds Chunk.Width x
  hy : Entity.InBounds Chunk.Height y
  hz : Entity.InBounds Chunk.Depth z

/-- An entity at the given position, if that position lies inside a chunk. -/
def Entity.at? (id kind : Nat) (chunk : Chunk.Coord) (x y z : Float) : Option Entity :=
  if hx : Entity.InBounds Chunk.Width x then
    if hy : Entity.InBounds Chunk.Height y then
      if hz : Entity.InBounds Chunk.Depth z then
        some { id, kind, chunk, x, y, z, hx, hy, hz }
      else none
    else none
  else none

/-- The same entity at another position, if that position lies inside a chunk. -/
def Entity.moveTo? (e : Entity) (chunk : Chunk.Coord) (x y z : Float) : Option Entity :=
  Entity.at? e.id e.kind chunk x y z

end Mathcraft
