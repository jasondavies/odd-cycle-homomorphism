module

public import TreewidthHom.GraftDecomposition

@[expose] public section

/-!
# Grafting indexed paths of bags

Each chain has its own old attachment point. A new bag contains its own vertex,
possibly its predecessor, and any old boundary vertices. This gives shared
proofs of the unique-top condition and coverage of consecutive chain vertices.
-/
namespace TreewidthHom.ChainGraft
open SimpleGraph

variable {V L B : Type} {q : ℕ}

/-- The first vertex follows the chosen old endpoint; later vertices follow
their predecessor in the same chain. -/
def prev (start : L → V) (p : L × Fin q) : V ⊕ (L × Fin q) :=
  if h : p.2.val = 0 then .inl (start p.1)
  else .inr (p.1, ⟨p.2.val-1, by have := p.2.isLt; omega⟩)

/-- Attach one chain of length `q` below each owning bag. -/
def graft (q : ℕ) (owner : L → B) : Graft B (L × Fin q) where
  parent := prev owner
  height p := p.2.val
  decreases := by
    intro p r h
    dsimp [prev] at h
    split_ifs at h with hz
    have he := congrArg (fun x : L × Fin q => x.2.val) (Sum.inr.inj h)
    dsimp at he ⊢
    omega

/-- A private predecessor is independent of the old attachment points. -/
theorem parent_of_prev (start : L → V) (owner : L → B) {p r : L × Fin q}
    (h : prev start p = .inr r) : (graft q owner).parent p = .inr r := by
  dsimp [prev] at h
  split_ifs at h with hz
  simpa [graft, prev, hz] using h

theorem prev_step (start : L → V) {p r : L × Fin q}
    (he : p.1 = r.1) (hh : r.2.val = p.2.val+1) : prev start r = .inr p := by
  have hz : r.2.val ≠ 0 := by omega
  simp only [prev, hz, ↓reduceDIte, Sum.inr.injEq]
  exact Prod.ext he.symm (Fin.ext (by simp; omega))

variable [DecidableEq V] {G : SimpleGraph V} {T : SimpleGraph B}
variable (D : Decomposition G T) (start : L → V) (bag : L × Fin q → Finset (V ⊕ (L × Fin q)))
variable (hmem : ∀ r p, Sum.inr r ∈ bag p ↔ r = p ∨ prev start p = Sum.inr r)

include hmem

/-- Every new vertex has its own bag as its only possible topmost occurrence. -/
theorem top (owner : L → B) {r p : L × Fin q}
    (hm : Sum.inr r ∈ bag p)
    (hn : Sum.inr r ∉ graftBag D bag ((graft q owner).parent p)) : r = p := by
  rcases (hmem r p).mp hm with he | he
  · exact he
  · apply False.elim
    apply hn
    rw [parent_of_prev start owner he, graftBag_inr]
    exact (hmem r r).mpr (Or.inl rfl)

/-- The unique-top hypothesis needed by `Graft.extend`. -/
theorem unique_top (owner : L → B) (r p p' : L × Fin q)
    (hp : Sum.inr r ∈ bag p)
    (hn : Sum.inr r ∉ graftBag D bag ((graft q owner).parent p))
    (hp' : Sum.inr r ∈ bag p')
    (hn' : Sum.inr r ∉ graftBag D bag ((graft q owner).parent p')) : p = p' :=
  (top D start bag hmem owner hp hn).symm.trans (top D start bag hmem owner hp' hn')

/-- Adjacent positions of a chain share the bag of the later vertex. -/
theorem edge_cover {p r : L × Fin q} (he : p.1 = r.1)
    (hh : r.2.val = p.2.val+1 ∨ p.2.val = r.2.val+1) :
    ∃ b, Sum.inr p ∈ graftBag D bag b ∧ Sum.inr r ∈ graftBag D bag b := by
  rcases hh with hh | hh
  · exact ⟨.inr r, (hmem p r).mpr (Or.inr (prev_step start he hh)),
      (hmem r r).mpr (Or.inl rfl)⟩
  · exact ⟨.inr p, (hmem p p).mpr (Or.inl rfl),
      (hmem r p).mpr (Or.inr (prev_step start he.symm hh))⟩

end TreewidthHom.ChainGraft
