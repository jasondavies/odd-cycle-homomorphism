module

public import TreewidthHom.ListReduction
public import TreewidthHom.LinkedWidth
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

/-- Rearrange hubs, shared vertices, and private reference vertices. -/
def layout : ((Fin m ⊕ Fin 2) ⊕ Private m n) ≃ BaseVertex m n where
  toFun
    | .inl (.inl v) => .inr v
    | .inl (.inr a) => .inl (.inl a)
    | .inr p => .inl (.inr p)
  invFun
    | .inr v => .inl (.inl v)
    | .inl (.inl a) => .inl (.inr a)
    | .inl (.inr p) => .inr p
  left_inv := by rintro ((v | a) | p) <;> rfl
  right_inv := by rintro ((a | p) | v) <;> rfl

/-- Add the shared edge to all old bags; sweep each reference path with its hub. -/
theorem aug_width (F : SimpleGraph (Fin m)) {w : ℕ} (hw : HasWidth F w) :
    HasWidth (aug (n := n) F) (max (w+2) 4) := by
  classical
  obtain ⟨d,B,T,D,hw⟩ := hw
  let H := (aug (n := n) F).comap layout
  let G0 : SimpleGraph (Fin m ⊕ Fin 2) := H.comap Sum.inl
  let D0 := D.addApices G0 (fun {u v} h => h)
  choose owner ho using D.vertex_cover
  let start : Copies m n → Fin m ⊕ Fin 2 := fun i => .inl i.1
  let prev : Private m n → ((Fin m ⊕ Fin 2) ⊕ Private m n) := ChainGraft.prev start
  let A := ChainGraft.graft (n-2) (fun i : Copies m n => owner i.1)
  let boundary : Private m n → Finset ((Fin m ⊕ Fin 2) ⊕ Private m n) := fun p =>
    {.inl (.inl p.1.1),.inl (.inr 0),.inl (.inr 1)}
  let bag : Private m n → Finset ((Fin m ⊕ Fin 2) ⊕ Private m n) := fun p =>
    boundary p ∪ {Sum.inr p,prev p}
  have own : ∀ p, Sum.inr p ∈ bag p := by intro p; simp [bag]
  have new_mem : ∀ r p, Sum.inr r ∈ bag p ↔ r = p ∨ prev p = Sum.inr r := by
    intro r p; simp [bag, boundary, eq_comm]
  have old_mem : ∀ v p, Sum.inl v ∈ bag p ↔ v = .inl p.1.1 ∨ ∃ a, v = .inr a := by
    intro v p
    cases v with
    | inl v => by_cases hz : p.2.val=0 <;> simp [bag,boundary,prev,ChainGraft.prev,start,hz]
    | inr a =>
      have ha : a=0 ∨ a=1 := by fin_cases a <;> simp
      rcases ha with rfl | rfl <;> simp [bag,boundary]
  have mixed : ∀ (v : Fin m ⊕ Fin 2) p, H.Adj (.inl v) (.inr p) → Sum.inl v ∈ bag p := by
    intro v p h
    apply (old_mem v p).mpr
    cases v with
    | inl v =>
      obtain ⟨d,he⟩ : ∃ d, Sum.inr p = ref (v,d) d := h
      have hh := (ref_private he.symm).1
      left; exact congrArg Sum.inl (congrArg Prod.fst hh).symm
    | inr a => exact Or.inr ⟨a,rfl⟩
  let D1 := A.extend D0 H bag (fun p => ⟨p,own p⟩)
    (by
      rintro (u | p) (v | r) h
      · obtain ⟨b,hu,hv⟩ := D0.edge_cover h
        exact ⟨.inl b,by simpa using hu,by simpa using hv⟩
      · exact ⟨.inr r,mixed u r h,own r⟩
      · exact ⟨.inr p,own p,mixed v p h.symm⟩
      · obtain ⟨he,hh⟩ := private_adj h
        exact ChainGraft.edge_cover D0 start bag new_mem he hh)
    (by
      intro v p hv
      have hv' := (old_mem v p).mp hv
      by_cases hz : p.2.val=0
      · have hp : A.parent p = .inl (owner p.1.1) := by simp [A,ChainGraft.graft,ChainGraft.prev,hz]
        rw [hp,graftBag_inl_inl]
        rcases hv' with rfl | ⟨a,rfl⟩
        · exact (D.inl_mem_apexBag _ _).mpr (ho _)
        · exact D.inr_mem_apexBag _ _
      · simp only [A,ChainGraft.graft,ChainGraft.prev,hz,↓reduceDIte,graftBag_inr]
        apply (old_mem _ _).mpr
        exact hv')
    (ChainGraft.unique_top D0 start bag new_mem (fun i : Copies m n => owner i.1))
  have he : ∀ u v, (aug F).Adj (layout u) (layout v) → H.Adj u v := fun _ _ h => h
  refine ⟨inferInstance,_,_,D1.mapEquiv layout he,fun b => ?_⟩
  rw [Decomposition.mapEquiv_card]
  apply graftBag_card D0 bag (k := w+2) (m := 4) ?_ ?_
  · intro b
    exact D.two_apex_width hw (by simp) b
  · intro p
    have h1 : (boundary p).card ≤ 3 := Finset.card_le_three
    have h2 : ({Sum.inr p,prev p} : Finset ((Fin m ⊕ Fin 2) ⊕ Private m n)).card ≤ 2 := Finset.card_le_two
    have h3 := Finset.card_union_le (boundary p) {Sum.inr p,prev p}
    change (boundary p ∪ {Sum.inr p,prev p}).card ≤ 5
    omega

theorem source_width (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    {w : ℕ} (hw : HasWidth F w) :
    HasWidth (source F L) (max (w+2) 4) := by
  classical
  obtain ⟨d,B,T,D,hw⟩ := aug_width (n := n) F hw
  choose owner hs ht using fun l : Link F L => D.edge_cover (link_adj_aug F L l)
  have h := width_linked_of_bags D (base m n) (base_le_aug F)
    (fun l : Link F L => src l.val) (fun l => dst l.val) (n-3) (max (w+2) 4)
    hw owner hs ht
  exact h.mono (by omega)

end TreewidthHom.OddCycle.ListReduction
