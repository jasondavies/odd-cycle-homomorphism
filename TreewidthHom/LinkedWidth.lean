module

public import TreewidthHom.GraftDecomposition
public import TreewidthHom.Width
public import TreewidthHom.Links

@[expose] public section

namespace TreewidthHom
open SimpleGraph

/-- Subdividing edges, or adding paths whose ends already share a bag, requires
only new bags of size three. -/
theorem width_linked_of_bags {V L B : Type} [DecidableEq V]
    {G : SimpleGraph V} {T : SimpleGraph B} (D : Decomposition G T)
    (H : SimpleGraph V) (hH : H ≤ G) (s t : L → V) (q w : ℕ) (_hq : 0 < q)
    (hw : ∀ b, (D.bag b).card ≤ w+1)
    (owner : L → B) (hs : ∀ l, s l ∈ D.bag (owner l))
    (ht : ∀ l, t l ∈ D.bag (owner l)) :
    HasWidth (linked H s t q) (max w 2) := by
  classical
  let prev : (L × Fin q) → V ⊕ (L × Fin q) := fun p =>
    if h : p.2.val = 0 then .inl (s p.1)
    else .inr (p.1,⟨p.2.val-1,by have := p.2.isLt; omega⟩)
  let F : Graft B (L × Fin q) :=
    { parent := fun p => if h : p.2.val = 0 then .inl (owner p.1)
        else .inr (p.1,⟨p.2.val-1,by have := p.2.isLt; omega⟩)
      height := fun p => p.2.val
      decreases := by
        intro p r h
        split_ifs at h with hz
        have he := congrArg (fun x : L × Fin q => x.2.val) (Sum.inr.inj h)
        dsimp at he ⊢
        omega }
  let bag : L × Fin q → Finset (V ⊕ (L × Fin q)) := fun p =>
    {Sum.inl (t p.1),Sum.inr p,prev p}
  have own : ∀ p, Sum.inr p ∈ bag p := by intro p; simp [bag]
  have back : ∀ p r, prev p = Sum.inr r → F.parent p = Sum.inr r := by
    intro p r h
    dsimp [prev] at h
    split_ifs at h with hz
    simpa [F,hz] using h
  have top : ∀ r p, Sum.inr r ∈ bag p →
      Sum.inr r ∉ graftBag D bag (F.parent p) → r = p := by
    intro r p hm hn
    have he : r = p ∨ prev p = Sum.inr r := by simpa [bag,eq_comm] using hm
    rcases he with he | he
    · exact he
    · exact False.elim (hn (by rw [back p r he,graftBag_inr]; exact own r))
  let D' := F.extend D (linked H s t q) bag (fun p => ⟨p,own p⟩)
    (by
      have mixed : ∀ x p, (p.2.val = 0 ∧ x = s p.1) ∨ (p.2.val+1 = q ∧ x = t p.1) →
          ∃ b, Sum.inl x ∈ graftBag D bag b ∧ Sum.inr p ∈ graftBag D bag b := by
        intro x p h
        refine ⟨.inr p,?_,own p⟩
        rcases h with ⟨hz,rfl⟩ | ⟨_,rfl⟩
        · simp [bag,prev,hz]
        · simp [bag]
      rintro (x | p) (y | r) h
      · obtain ⟨b,hx,hy⟩ := D.edge_cover (hH h)
        exact ⟨.inl b,by simpa using hx,by simpa using hy⟩
      · exact mixed x r h
      · obtain ⟨b,hx,hy⟩ := mixed y p h
        exact ⟨b,hy,hx⟩
      · obtain ⟨he,hh⟩ : p.1 = r.1 ∧ (r.2.val = p.2.val+1 ∨ p.2.val = r.2.val+1) := h
        have step : ∀ p r : L × Fin q, p.1 = r.1 → r.2.val = p.2.val+1 →
            prev r = Sum.inr p := by
          intro p r he hh
          have hz : r.2.val ≠ 0 := by omega
          simp only [prev,hz,↓reduceDIte,Sum.inr.injEq]
          exact Prod.ext he.symm (Fin.ext (by simp; omega))
        rcases hh with hh | hh
        · exact ⟨.inr r,by simp [bag,step p r he hh],own r⟩
        · exact ⟨.inr p,own p,by simp [bag,step r p he.symm hh]⟩)
    (by
      intro v p hv
      have hv' : v = t p.1 ∨ prev p = Sum.inl v := by simpa [bag,eq_comm] using hv
      by_cases hz : p.2.val = 0
      · change Sum.inl v ∈ graftBag D bag (F.parent p)
        have hp : F.parent p = Sum.inl (owner p.1) := by simp [F,hz]
        rw [hp,graftBag_inl_inl]
        rcases hv' with rfl | h
        · exact ht p.1
        · have he : s p.1 = v := by simpa [prev,hz] using h
          rw [← he]; exact hs p.1
      · have he : v = t p.1 := hv'.resolve_right (by simp [prev,hz])
        subst v
        simp [F,hz,bag])
    (by intro r p p' hp hn hp' hn'; exact (top r p hp hn).symm.trans (top r p' hp' hn'))
  exact ⟨inferInstance,_,_,D',graftBag_card D bag hw (fun _ => Finset.card_le_three)⟩

end TreewidthHom
