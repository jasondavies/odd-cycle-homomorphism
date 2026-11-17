module

public import TreewidthHom.ChainGraft
public import TreewidthHom.Width
public import TreewidthHom.Links

@[expose] public section

namespace TreewidthHom
open SimpleGraph

/-- Subdividing edges, or adding paths whose ends already share a bag, requires
only new bags of size three. -/
theorem decomposition_linked_of_bags {V L B : Type} [DecidableEq V] [DecidableEq L]
    {G : SimpleGraph V} {T : SimpleGraph B} (D : Decomposition G T)
    (H : SimpleGraph V) (hH : H ≤ G) (s t : L → V) (q w : ℕ)
    (hw : ∀ b, (D.bag b).card ≤ w+1)
    (owner : L → B) (hs : ∀ l, s l ∈ D.bag (owner l))
    (ht : ∀ l, t l ∈ D.bag (owner l)) :
    ∃ T' : SimpleGraph (B ⊕ (L × Fin q)), ∃ D' : Decomposition (linked H s t q) T',
      ∀ b, (D'.bag b).card ≤ max w 2 + 1 := by
  classical
  let prev : (L × Fin q) → V ⊕ (L × Fin q) := ChainGraft.prev s
  let F := ChainGraft.graft q owner
  let bag : L × Fin q → Finset (V ⊕ (L × Fin q)) := fun p =>
    {Sum.inl (t p.1),Sum.inr p,prev p}
  have own : ∀ p, Sum.inr p ∈ bag p := by intro p; simp [bag]
  have new_mem : ∀ r p, Sum.inr r ∈ bag p ↔ r = p ∨ prev p = Sum.inr r := by
    intro r p; simp [bag, eq_comm]
  let D' := F.extend D (linked H s t q) bag (fun p => ⟨p,own p⟩)
    (by
      have mixed : ∀ x p, (p.2.val = 0 ∧ x = s p.1) ∨ (p.2.val+1 = q ∧ x = t p.1) →
          ∃ b, Sum.inl x ∈ graftBag D bag b ∧ Sum.inr p ∈ graftBag D bag b := by
        intro x p h
        refine ⟨.inr p,?_,own p⟩
        rcases h with ⟨hz,rfl⟩ | ⟨_,rfl⟩
        · simp [bag,prev,ChainGraft.prev,hz]
        · simp [bag]
      rintro (x | p) (y | r) h
      · obtain ⟨b,hx,hy⟩ := D.edge_cover (hH h)
        exact ⟨.inl b,by simpa using hx,by simpa using hy⟩
      · exact mixed x r h
      · obtain ⟨b,hx,hy⟩ := mixed y p h
        exact ⟨b,hy,hx⟩
      · obtain ⟨he,hh⟩ : p.1 = r.1 ∧ (r.2.val = p.2.val+1 ∨ p.2.val = r.2.val+1) := h
        exact ChainGraft.edge_cover D s bag new_mem he hh)
    (by
      intro v p hv
      have hv' : v = t p.1 ∨ prev p = Sum.inl v := by simpa [bag,eq_comm] using hv
      by_cases hz : p.2.val = 0
      · change Sum.inl v ∈ graftBag D bag (F.parent p)
        have hp : F.parent p = Sum.inl (owner p.1) := by simp [F,ChainGraft.graft,ChainGraft.prev,hz]
        rw [hp,graftBag_inl_inl]
        rcases hv' with rfl | h
        · exact ht p.1
        · have he : s p.1 = v := by simpa [prev,ChainGraft.prev,hz] using h
          rw [← he]; exact hs p.1
      · have he : v = t p.1 := hv'.resolve_right (by simp [prev,ChainGraft.prev,hz])
        subst v
        simp [F,ChainGraft.graft,ChainGraft.prev,hz,bag])
    (ChainGraft.unique_top D s bag new_mem owner)
  exact ⟨_,D',graftBag_card D bag hw (fun _ => Finset.card_le_three)⟩

/-- The width bound obtained by forgetting the explicit output index type. -/
theorem width_linked_of_bags {V L B : Type} [DecidableEq V]
    {G : SimpleGraph V} {T : SimpleGraph B} (D : Decomposition G T)
    (H : SimpleGraph V) (hH : H ≤ G) (s t : L → V) (q w : ℕ)
    (hw : ∀ b, (D.bag b).card ≤ w+1)
    (owner : L → B) (hs : ∀ l, s l ∈ D.bag (owner l))
    (ht : ∀ l, t l ∈ D.bag (owner l)) :
    HasWidth (linked H s t q) (max w 2) := by
  classical
  obtain ⟨T', D', hD'⟩ := decomposition_linked_of_bags D H hH s t q w hw owner hs ht
  exact ⟨inferInstance, B ⊕ (L × Fin q), T', D', hD'⟩

end TreewidthHom
