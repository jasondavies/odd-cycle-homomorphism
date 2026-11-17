module

public import TreewidthHom.GraftDecomposition
public import TreewidthHom.Width

@[expose] public section

namespace TreewidthHom
open SimpleGraph

/-- The graft construction adds exactly one index for each attached vertex. -/
theorem Graft.decomposition_of_bags {V P B : Type} [DecidableEq V] [DecidableEq P]
    (F : Graft V P) {G : SimpleGraph V} {T : SimpleGraph B}
    (D : Decomposition G T) {w : ℕ} (hw : ∀ b, (D.bag b).card ≤ w+1) :
    ∃ T' : SimpleGraph (B ⊕ P), ∃ D' : Decomposition (F.graph G) T',
      ∀ b, (D'.bag b).card ≤ max w 1 + 1 := by
  classical
  choose owner ho using D.vertex_cover
  let A : Graft B P :=
    { parent := fun p => (F.parent p).map owner id
      height := F.height
      decreases := by
        intro p q h
        cases hp : F.parent p with
        | inl v => simp [hp] at h
        | inr r =>
          have he : r = q := by simpa [hp] using h
          exact F.decreases p q (hp.trans (congrArg Sum.inr he)) }
  let bag : P → Finset (V ⊕ P) := fun p => {Sum.inr p,F.parent p}
  have own : ∀ p, Sum.inr p ∈ bag p := by intro p; simp [bag]
  have parent_mem : ∀ p, F.parent p ∈ bag p := by intro p; simp [bag]
  have top : ∀ q p, Sum.inr q ∈ bag p →
      Sum.inr q ∉ graftBag D bag (A.parent p) → q = p := by
    intro q p hm hn
    have hm' : q = p ∨ Sum.inr q = F.parent p := by simpa [bag] using hm
    rcases hm' with h | h
    · exact h
    · exfalso
      apply hn
      simpa [A,← h] using own q
  let D' := A.extend D (F.graph G) bag (fun p => ⟨p,own p⟩)
    (by
      rintro (u | p) (v | q) h
      · obtain ⟨b,hu,hv⟩ := D.edge_cover h
        exact ⟨.inl b,by simpa using hu,by simpa using hv⟩
      · have hp : F.parent q = .inl u := h
        exact ⟨.inr q,by simpa [hp] using parent_mem q,own q⟩
      · have hp : F.parent p = .inl v := h
        exact ⟨.inr p,own p,by simpa [hp] using parent_mem p⟩
      · rcases h with h | h
        · exact ⟨.inr p,own p,by simpa [h] using parent_mem p⟩
        · exact ⟨.inr q,by simpa [h] using parent_mem q,own q⟩)
    (by
      intro v p hv
      have hp : F.parent p = .inl v := by simpa [bag,eq_comm] using hv
      simpa [A,hp] using ho v)
    (fun q p p' hp hn hp' hn' => (top q p hp hn).symm.trans (top q p' hp' hn'))
  exact ⟨_,D',graftBag_card D bag hw (fun _ => Finset.card_le_two)⟩

/-- Attaching rooted trees at single vertices gives width at most `max w 1`. -/
theorem Graft.hasWidth {V P : Type} (F : Graft V P) {G : SimpleGraph V}
    {w : ℕ} (hw : HasWidth G w) : HasWidth (F.graph G) (max w 1) := by
  classical
  obtain ⟨d, B, T, D, hw⟩ := hw
  let := d
  obtain ⟨T', D', hD'⟩ := F.decomposition_of_bags D hw
  exact ⟨inferInstance, B ⊕ P, T', D', hD'⟩

end TreewidthHom
