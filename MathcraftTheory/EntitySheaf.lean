import MathcraftTheory.ChunkTopology
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The sheaf of entities

A section over an open set `U` is a set of entities located in `U`, and restricting to `V ≤ U`
forgets the entities outside of `V`. This presheaf is a sheaf.

Different chunks don't overlap, so sections over different chunks are always compatible, and
gluing alone can't relate them. An entity moving between chunks is encoded by what gluing makes
possible: glue the sections of both chunks to a section over their union, move the entity inside
that section, and restrict back to the chunks. See `moveBetweenChunks`.
-/

namespace Mathcraft

open TopologicalSpace CategoryTheory Opposite TopCat TopCat.Presheaf

/-- The blocks of a world as a topological space. -/
abbrev WorldSpace : TopCat := TopCat.of BlockPosition

/-- The entities located in `U`. -/
def EntitySection (U : Opens WorldSpace) : Type :=
  {s : Set Entity // ∀ e ∈ s, e.block ∈ U}

namespace EntitySection

theorem ext {U : Opens WorldSpace} {s t : EntitySection U} (h : ∀ e, e ∈ s.1 ↔ e ∈ t.1) : s = t :=
  Subtype.ext (Set.ext h)

/-- The entities of `s` that are located in `V`. -/
def restrict {U V : Opens WorldSpace} (h : V ≤ U) (s : EntitySection U) : EntitySection V :=
  ⟨{e ∈ s.1 | e.block ∈ V}, fun _ he ↦ he.2⟩

end EntitySection

/-- The presheaf of entities. -/
def entityPresheaf : TopCat.Presheaf (Type) WorldSpace where
  obj U := EntitySection U.unop
  map f := EntitySection.restrict (leOfHom f.unop)
  map_id U := by
    funext s
    exact EntitySection.ext fun e ↦ and_iff_left_of_imp (s.2 e)
  map_comp f g := by
    funext s
    exact EntitySection.ext fun e ↦
      ⟨fun h ↦ ⟨⟨h.1, leOfHom g.unop h.2⟩, h.2⟩, fun h ↦ ⟨h.1.1, h.2⟩⟩

/-- Locality and gluing: the presheaf of entities is a sheaf. -/
theorem entityPresheaf_isSheaf : entityPresheaf.IsSheaf := by
  refine isSheaf_of_isSheafUniqueGluing_types _ ?_
  intro ι U sf compatible
  have shared : ∀ i j e, e ∈ (sf i).1 → e.block ∈ U j → e ∈ (sf j).1 := by
    intro i j e hi hj
    have h := congrArg Subtype.val (compatible i j)
    have mem : e ∈ {x ∈ (sf i).1 | x.block ∈ U i ⊓ U j} := ⟨hi, (sf i).2 e hi, hj⟩
    exact (Set.ext_iff.1 h e).1 mem |>.1
  refine ⟨⟨⋃ i, (sf i).1, ?_⟩, ?_, ?_⟩
  · intro e he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
    exact Opens.mem_iSup.2 ⟨i, (sf i).2 e hi⟩
  · intro i
    refine EntitySection.ext fun e ↦ ⟨?_, fun he ↦ ⟨Set.mem_iUnion.2 ⟨i, he⟩, (sf i).2 e he⟩⟩
    rintro ⟨he, hi⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 he
    exact shared j i e hj hi
  · intro t ht
    refine EntitySection.ext fun e ↦ ⟨fun he ↦ ?_, fun he ↦ ?_⟩
    · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (t.2 e he)
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      have h := congrArg Subtype.val (ht i)
      exact (Set.ext_iff.1 h e).1 ⟨he, hi⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
      have h := congrArg Subtype.val (ht i)
      exact ((Set.ext_iff.1 h e).2 hi).1

/-- The sheaf of entities. -/
def entitySheaf : TopCat.Sheaf (Type) WorldSpace := ⟨entityPresheaf, entityPresheaf_isSheaf⟩

section Moves

variable {U : Opens WorldSpace}

/-- `s` with the entity `e` moved to the block `p`, which has to lie in `U`. -/
def EntitySection.move (s : EntitySection U) (e : Entity) (p : BlockPosition)
    (hp : p ∈ U) : EntitySection U :=
  ⟨insert (e.moveTo p) (s.1 \ {e}), by
    rintro x (rfl | hx)
    · exact hp
    · exact s.2 x hx.1⟩

/-- Moving an entity doesn't create or destroy anything: the same ids exist before and after. -/
theorem EntitySection.ids_move (s : EntitySection U) {e : Entity} (he : e ∈ s.1)
    (p : BlockPosition) (hp : p ∈ U) :
    Entity.id '' (s.move e p hp).1 = Entity.id '' s.1 := by
  ext n
  constructor
  · rintro ⟨x, rfl | hx, rfl⟩
    · exact ⟨e, he, rfl⟩
    · exact ⟨x, hx.1, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    by_cases h : x = e
    · subst h
      exact ⟨x.moveTo p, Or.inl rfl, rfl⟩
    · exact ⟨x, Or.inr ⟨hx, h⟩, rfl⟩

/-- A move only changes the sections over open sets around where it happens. -/
theorem EntitySection.restrict_move (s : EntitySection U) {V : Opens WorldSpace} (hV : V ≤ U)
    {e : Entity} {p : BlockPosition} (hp : p ∈ U) (he : e.block ∉ V) (hpV : p ∉ V) :
    (s.move e p hp).restrict hV = s.restrict hV := by
  refine EntitySection.ext fun x ↦ ⟨?_, ?_⟩
  · rintro ⟨rfl | hx, hxV⟩
    · exact absurd hxV hpV
    · exact ⟨hx.1, hxV⟩
  · rintro ⟨hx, hxV⟩
    refine ⟨Or.inr ⟨hx, ?_⟩, hxV⟩
    rintro rfl
    exact he hxV

/-- The open set made up of two chunks. -/
def chunkPair (a b : Chunk.Coord) : Opens WorldSpace := chunkOpen a ⊔ chunkOpen b

theorem chunk_le_left (a b : Chunk.Coord) : chunkOpen a ≤ chunkPair a b := le_sup_left

theorem chunk_le_right (a b : Chunk.Coord) : chunkOpen b ≤ chunkPair a b := le_sup_right

/-- Sections over two different chunks glue to the entities of both. -/
def glueChunks {a b : Chunk.Coord} (sa : EntitySection (chunkOpen a))
    (sb : EntitySection (chunkOpen b)) : EntitySection (chunkPair a b) :=
  ⟨sa.1 ∪ sb.1, by
    rintro e (he | he)
    · exact chunk_le_left a b (sa.2 e he)
    · exact chunk_le_right a b (sb.2 e he)⟩

theorem restrict_glueChunks_left {a b : Chunk.Coord} (hab : a ≠ b)
    (sa : EntitySection (chunkOpen a)) (sb : EntitySection (chunkOpen b)) :
    (glueChunks sa sb).restrict (chunk_le_left a b) = sa := by
  refine EntitySection.ext fun e ↦ ⟨?_, fun he ↦ ⟨Or.inl he, sa.2 e he⟩⟩
  rintro ⟨he | he, hea⟩
  · exact he
  · exact absurd (Eq.trans (Eq.symm (sb.2 e he)) hea) hab.symm

theorem restrict_glueChunks_right {a b : Chunk.Coord} (hab : a ≠ b)
    (sa : EntitySection (chunkOpen a)) (sb : EntitySection (chunkOpen b)) :
    (glueChunks sa sb).restrict (chunk_le_right a b) = sb := by
  refine EntitySection.ext fun e ↦ ⟨?_, fun he ↦ ⟨Or.inr he, sb.2 e he⟩⟩
  rintro ⟨he | he, heb⟩
  · exact absurd (Eq.trans (Eq.symm (sa.2 e he)) heb) hab
  · exact he

/--
Moves the entity `e` to the block `p` of the chunk `b`: glue the sections of both chunks,
move `e` in the glued section, and restrict the result to the chunks again.
-/
def moveBetweenChunks {a b : Chunk.Coord} (sa : EntitySection (chunkOpen a))
    (sb : EntitySection (chunkOpen b)) (e : Entity) (p : BlockPosition) (hp : p.chunk = b) :
    EntitySection (chunkOpen a) × EntitySection (chunkOpen b) :=
  let moved := (glueChunks sa sb).move e p (chunk_le_right a b hp)
  (moved.restrict (chunk_le_left a b), moved.restrict (chunk_le_right a b))

/-- `moveBetweenChunks` takes `e` out of the first chunk... -/
theorem moveBetweenChunks_left {a b : Chunk.Coord} (hab : a ≠ b)
    (sa : EntitySection (chunkOpen a)) (sb : EntitySection (chunkOpen b)) {e : Entity}
    (p : BlockPosition) (hp : p.chunk = b) :
    (moveBetweenChunks sa sb e p hp).1.1 = sa.1 \ {e} := by
  ext x
  constructor
  · rintro ⟨rfl | ⟨hx | hx, hne⟩, hxa⟩
    · exact absurd (Eq.trans (Eq.symm hxa) hp) hab
    · exact ⟨hx, hne⟩
    · exact absurd (Eq.trans (Eq.symm (sb.2 x hx)) hxa) hab.symm
  · rintro ⟨hx, hne⟩
    exact ⟨Or.inr ⟨Or.inl hx, hne⟩, sa.2 x hx⟩

/-- ...and puts it into the second one, leaving the entities that were already there. -/
theorem moveBetweenChunks_right {a b : Chunk.Coord} (hab : a ≠ b)
    (sa : EntitySection (chunkOpen a)) (sb : EntitySection (chunkOpen b)) {e : Entity}
    (he : e ∈ sa.1) (p : BlockPosition) (hp : p.chunk = b) :
    (moveBetweenChunks sa sb e p hp).2.1 = insert (e.moveTo p) sb.1 := by
  ext x
  constructor
  · rintro ⟨rfl | ⟨hx | hx, -⟩, hxb⟩
    · exact Or.inl rfl
    · exact absurd (Eq.trans (Eq.symm (sa.2 x hx)) hxb) hab
    · exact Or.inr hx
  · rintro (rfl | hx)
    · exact ⟨Or.inl rfl, hp⟩
    · refine ⟨Or.inr ⟨Or.inr hx, ?_⟩, sb.2 x hx⟩
      rintro rfl
      exact hab (Eq.trans (Eq.symm (sa.2 _ he)) (sb.2 _ hx))

end Moves

end Mathcraft
