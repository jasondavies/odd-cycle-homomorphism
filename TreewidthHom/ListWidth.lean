module

public import TreewidthHom.ListReduction
public import TreewidthHom.LinkedWidth
public import TreewidthHom.GraftWidth
public import TreewidthHom.DecompositionMaps

@[expose] public section

namespace TreewidthHom.OddCycle.ListReduction
open SimpleGraph Reference
variable {m n : ℕ} [Fact (1 < n)]

/-- The auxiliary graph contains the original edges and unsubdivided list links. -/
def aug (F : SimpleGraph (Fin m)) : SimpleGraph (BaseVertex m n) where
  Adj
    | .inl x, .inl y => (base m n).Adj (.inl x) (.inl y)
    | .inr u, .inr v => F.Adj u v
    | .inl x, .inr v => ∃ d, x = ref (v,d) d
    | .inr v, .inl x => ∃ d, x = ref (v,d) d
  symm := ⟨by rintro (x | x) (y | y) h; exact h.symm; exact h; exact h; exact h.symm⟩
  loopless := ⟨by rintro (x | x) h; exact (base m n).loopless.irrefl _ h; exact F.loopless.irrefl _ h⟩

theorem base_le_aug (F : SimpleGraph (Fin m)) : base m n ≤ aug F := by
  rintro (x | x) (y | y) h
  · exact h
  all_goals obtain ⟨_,h | h⟩ := (fromRel_adj _ _ _).mp h <;> exact h.elim

theorem link_adj_aug (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n)) (l : Link F L) :
    (aug F).Adj (src l.val) (dst l.val) := by
  rcases l with ⟨(⟨v,d⟩ | ⟨u,v⟩),h⟩
  · exact ⟨d,rfl⟩
  · exact h.2

/-- The reference paths root at their domain-link coordinate, or at coordinate
2 when that coordinate is one of the anchors. -/
def referenceParent (p : Private m n) : Fin m ⊕ Private m n :=
  if h : p.2.val < p.1.2.val-2 then
    .inr (p.1,⟨p.2.val+1,by have := ZMod.val_lt p.1.2; omega⟩)
  else if h : p.1.2.val-2 < p.2.val then
    .inr (p.1,⟨p.2.val-1,by have := p.2.isLt; omega⟩)
  else .inl p.1.1

def referenceGraft (m n : ℕ) [Fact (1 < n)] : Graft (Fin m) (Private m n) where
  parent := referenceParent
  height p := (p.2.val-(p.1.2.val-2))+((p.1.2.val-2)-p.2.val)
  decreases := by
    intro p r h
    dsimp [referenceParent] at h
    split_ifs at h with h1 h2
    · cases Sum.inr.inj h
      dsimp
      omega
    · cases Sum.inr.inj h
      dsimp
      omega

theorem reference_parent_root {p : Private m n} (h : p.2.val = p.1.2.val-2) :
    referenceParent p = .inl p.1.1 := by simp [referenceParent,h]

theorem reference_parent_step {p r : Private m n}
    (he : p.1 = r.1) (hh : r.2.val = p.2.val+1) :
    referenceParent p = .inr r ∨ referenceParent r = .inr p := by
  by_cases h : p.2.val < p.1.2.val-2
  · left
    simp only [referenceParent,h,↓reduceDIte,Sum.inr.injEq]
    exact Prod.ext he (Fin.ext (by simp; omega))
  · right
    have h1 : ¬ r.2.val < r.1.2.val-2 := by rw [← he]; omega
    have h2 : r.1.2.val-2 < r.2.val := by rw [← he]; omega
    simp only [referenceParent,h1,h2,↓reduceDIte,Sum.inr.injEq]
    exact Prod.ext he.symm (Fin.ext (by simp; omega))

/-- Put the two anchors outside the graph of hubs and attached reference trees. -/
def layout : ((Fin m ⊕ Private m n) ⊕ Fin 2) ≃ BaseVertex m n where
  toFun
    | .inl (.inl v) => .inr v
    | .inl (.inr p) => .inl (.inr p)
    | .inr a => .inl (.inl a)
  invFun
    | .inr v => .inl (.inl v)
    | .inl (.inr p) => .inl (.inr p)
    | .inl (.inl a) => .inr a
  left_inv := by rintro ((v | p) | a) <;> rfl
  right_inv := by rintro ((a | p) | v) <;> rfl

/-- Removing the anchors exposes the input graph with rooted trees attached;
adding the anchors back gives bags of size at most max(w+3,4). -/
theorem aug_decomposition {B : Type} [DecidableEq (Fin m)]
    (F : SimpleGraph (Fin m)) {T : SimpleGraph B} (D₀ : Decomposition F T)
    {w : ℕ} (hw : ∀ b, (D₀.bag b).card ≤ w+1) :
    ∃ T' : SimpleGraph (B ⊕ Private m n), ∃ D' : Decomposition (aug (n := n) F) T',
      ∀ b, (D'.bag b).card ≤ max (w+2) 3 + 1 := by
  classical
  obtain ⟨T₁,D,hD⟩ := (referenceGraft m n).decomposition_of_bags D₀ hw
  let H := (aug (n := n) F).comap layout
  have hbase : ∀ {u v}, H.Adj (.inl u) (.inl v) →
      ((referenceGraft m n).graph F).Adj u v := by
    have mixed : ∀ (v : Fin m) (p : Private m n),
        (∃ d, Sum.inr p = ref (v,d) d) → referenceParent p = .inl v := by
      intro v p ⟨d,he⟩
      obtain ⟨hi,hv⟩ := ref_private he.symm
      have hp : p.2.val = p.1.2.val-2 := by rw [hi]; dsimp; omega
      rw [reference_parent_root hp,hi]
    rintro (u | p) (v | r) h
    · exact h
    · exact mixed u r h
    · exact mixed v p h
    · obtain ⟨he,hh⟩ := private_adj h
      rcases hh with hh | hh
      · exact reference_parent_step he hh
      · exact (reference_parent_step he.symm hh).symm
  let D' := D.addApices H hbase
  have he : ∀ u v, (aug F).Adj (layout u) (layout v) → H.Adj u v := fun _ _ h => h
  refine ⟨_,D'.mapEquiv layout he,fun b => ?_⟩
  rw [Decomposition.mapEquiv_card]
  have h := D.two_apex_width hD (A := Fin 2) (by simp) b
  change (D.apexBag (A := Fin 2) b).card ≤ _
  omega

/-- Forgetting the explicit bag-index type recovers the width-only statement. -/
theorem aug_width (F : SimpleGraph (Fin m)) {w : ℕ} (hw : HasWidth F w) :
    HasWidth (aug (n := n) F) (max (w+2) 3) := by
  classical
  obtain ⟨d, B, T, D, hD⟩ := hw
  let := d
  obtain ⟨T', D', hD'⟩ := aug_decomposition (n := n) F D hD
  exact ⟨inferInstance, B ⊕ Private m n, T', D', hD'⟩

set_option synthInstance.maxSize 256 in
/-- The output indices consist of the input bags, one bag per private reference
vertex, and one bag per internal link vertex. -/
theorem source_decomposition {B : Type} [DecidableEq (Fin m)]
    (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    {T : SimpleGraph B} (D₀ : Decomposition F T)
    {w : ℕ} (hw : ∀ b, (D₀.bag b).card ≤ w+1) :
    ∃ T' : SimpleGraph ((B ⊕ Private m n) ⊕ (Link F L × Fin (n-3))),
      ∃ D' : Decomposition (source F L) T',
        ∀ b, (D'.bag b).card ≤ max (w+2) 3 + 1 := by
  classical
  obtain ⟨T₁, D, hD⟩ := aug_decomposition (n := n) F D₀ hw
  choose owner hs ht using fun l : Link F L => D.edge_cover (link_adj_aug F L l)
  obtain ⟨T', D', hD'⟩ := decomposition_linked_of_bags D (base m n) (base_le_aug F)
    (fun l : Link F L => src l.val) (fun l => dst l.val) (n-3) (max (w+2) 3)
    hD owner hs ht
  exact ⟨T', D', fun b => by have := hD' b; omega⟩

theorem source_width (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    {w : ℕ} (hw : HasWidth F w) :
    HasWidth (source F L) (max (w+2) 3) := by
  classical
  obtain ⟨d, B, T, D, hD⟩ := hw
  let := d
  obtain ⟨T', D', hD'⟩ := source_decomposition F L D hD
  exact ⟨_, _, T', D', hD'⟩

end TreewidthHom.OddCycle.ListReduction
