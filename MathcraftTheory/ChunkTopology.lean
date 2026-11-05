import «Mathcraft».model.Entity
import Mathlib.Topology.Bases

/-!
# The topology of chunks

The chunks form a basis of a topology on the blocks of a world: the open sets are exactly the
unions of chunks. See <https://happel.ai/posts/sheaves_in_minecraft/>.

Chunks are pairwise disjoint, so this topology is coarse: a chunk is the smallest open set around
each of its blocks, and blocks of one chunk can't be told apart by open sets.
-/

namespace Mathcraft

open TopologicalSpace Set

/-- The blocks of the chunk at `c`. -/
def chunkSet (c : Chunk.Coord) : Set BlockPosition := {p | p.chunk = c}

instance : TopologicalSpace BlockPosition := generateFrom (range chunkSet)

theorem chunkSet_disjoint {a b : Chunk.Coord} (h : a ≠ b) : Disjoint (chunkSet a) (chunkSet b) :=
  disjoint_left.2 fun _ ha hb ↦ h (ha.symm.trans hb)

/-- The chunks form a basis of the topology. -/
theorem isTopologicalBasis_chunks : IsTopologicalBasis (range chunkSet) where
  exists_subset_inter := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ p ⟨ha, hb⟩
    obtain rfl : a = b := Eq.trans (Eq.symm ha) hb
    exact ⟨_, mem_range_self a, ha, fun _ hq ↦ ⟨hq, hq⟩⟩
  sUnion_eq := eq_univ_of_forall fun p ↦ ⟨chunkSet p.chunk, mem_range_self _, rfl⟩
  eq_generateFrom := rfl

theorem isOpen_chunkSet (c : Chunk.Coord) : IsOpen (chunkSet c) :=
  isTopologicalBasis_chunks.isOpen (mem_range_self c)

/-- An open set containing a block contains the whole chunk of that block. -/
theorem chunkSet_subset_of_isOpen {U : Set BlockPosition} (hU : IsOpen U) {p : BlockPosition}
    (hp : p ∈ U) : chunkSet p.chunk ⊆ U := by
  obtain ⟨_, ⟨c, rfl⟩, hc, hsub⟩ := isTopologicalBasis_chunks.exists_subset_of_mem_open hp hU
  obtain rfl : p.chunk = c := hc
  exact hsub

/-- The chunk at `c` as an open set. -/
def chunkOpen (c : Chunk.Coord) : Opens BlockPosition := ⟨chunkSet c, isOpen_chunkSet c⟩

end Mathcraft
