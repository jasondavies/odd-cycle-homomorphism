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

abbrev Private (m n : ℕ) := Copies m n × Fin (n-2)

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

theorem private_step {i j : Copies m n} {a b : Fin (n-2)} {d : ZMod n}
    (ha : ref i d = .inr (i,a)) (hb : ref i (d+1) = .inr (j,b)) :
    i = j ∧ b.val = a.val+1 := by
  obtain ⟨_,hda⟩ := ref_private ha
  obtain ⟨hij,hdb⟩ := ref_private hb
  have hv : (d+1).val = (d.val+1)%n := by rw [ZMod.val_add,ZMod.val_one]
  have hd := ZMod.val_lt d
  refine ⟨hij.symm,?_⟩
  rcases Nat.lt_or_ge (d.val+1) n with hh | hh
  · rw [Nat.mod_eq_of_lt hh] at hv; omega
  · have : d.val+1=n := by omega
    rw [this,Nat.mod_self] at hv; omega

theorem private_adj {p r : Private m n}
    (h : (base m n).Adj (.inl (.inr p)) (.inl (.inr r))) :
    p.1 = r.1 ∧ (r.2.val = p.2.val+1 ∨ p.2.val = r.2.val+1) := by
  have step : ∀ p r : Private m n, BaseRel (.inl (.inr p)) (.inl (.inr r)) →
      p.1 = r.1 ∧ r.2.val = p.2.val+1 := by
    intro p r hh
    rcases hh with ⟨h,_⟩ | ⟨i,d,hp,hr⟩
    · cases h
    · have hi := (ref_private hp.symm).1
      have hp' : ref p.1 d = .inr (p.1,p.2) := by simpa [← hi] using hp.symm
      have hr' : ref p.1 (d+1) = .inr (r.1,r.2) := by simpa [← hi] using hr.symm
      exact private_step hp' hr'
  obtain ⟨_,h | h⟩ := (fromRel_adj _ _ _).mp h
  · obtain ⟨he,hh⟩ := step p r h; exact ⟨he,Or.inl hh⟩
  · obtain ⟨he,hh⟩ := step r p h; exact ⟨he.symm,Or.inr hh⟩

/-- Add the shared edge to all old bags; sweep each reference path with its hub. -/
theorem aug_width (F : SimpleGraph (Fin m)) {w : ℕ} (hw : HasWidth F w) :
    HasWidth (aug (n := n) F) (max (w+2) 4) := by
  classical
  obtain ⟨d,B,T,D,hw⟩ := hw
  let H := (aug (n := n) F).comap layout
  let G0 : SimpleGraph (Fin m ⊕ Fin 2) := H.comap Sum.inl
  let D0 := D.addApices G0 (fun {u v} h => h)
  choose owner ho using D.vertex_cover
  let prev : Private m n → ((Fin m ⊕ Fin 2) ⊕ Private m n) := fun p =>
    if h : p.2.val = 0 then .inl (.inl p.1.1)
    else .inr (p.1,⟨p.2.val-1,by have := p.2.isLt; omega⟩)
  let A : Graft B (Private m n) :=
    { parent := fun p => if h : p.2.val = 0 then .inl (owner p.1.1)
        else .inr (p.1,⟨p.2.val-1,by have := p.2.isLt; omega⟩)
      height := fun p => p.2.val
      decreases := by
        intro p r h
        split_ifs at h with hz
        have he := congrArg (fun x : Private m n => x.2.val) (Sum.inr.inj h)
        dsimp at he ⊢; omega }
  let boundary : Private m n → Finset ((Fin m ⊕ Fin 2) ⊕ Private m n) := fun p =>
    {.inl (.inl p.1.1),.inl (.inr 0),.inl (.inr 1)}
  let bag : Private m n → Finset ((Fin m ⊕ Fin 2) ⊕ Private m n) := fun p =>
    boundary p ∪ {Sum.inr p,prev p}
  have own : ∀ p, Sum.inr p ∈ bag p := by intro p; simp [bag]
  have back : ∀ p r, prev p = Sum.inr r → A.parent p = Sum.inr r := by
    intro p r h
    dsimp [prev] at h; split_ifs at h with hz
    simpa [A,hz] using h
  have top : ∀ r p, Sum.inr r ∈ bag p →
      Sum.inr r ∉ graftBag D0 bag (A.parent p) → r = p := by
    intro r p hm hn
    have he : r = p ∨ prev p = Sum.inr r := by simpa [bag,boundary,eq_comm] using hm
    rcases he with he | he
    · exact he
    · exact False.elim (hn (by rw [back p r he,graftBag_inr]; exact own r))
  have old_mem : ∀ v p, Sum.inl v ∈ bag p ↔ v = .inl p.1.1 ∨ ∃ a, v = .inr a := by
    intro v p
    cases v with
    | inl v => by_cases hz : p.2.val=0 <;> simp [bag,boundary,prev,hz]
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
        have step : ∀ p r : Private m n, p.1=r.1 → r.2.val=p.2.val+1 → prev r=.inr p := by
          intro p r he hh
          have hz : r.2.val ≠ 0 := by omega
          simp only [prev,hz,↓reduceDIte,Sum.inr.injEq]
          exact Prod.ext he.symm (Fin.ext (by simp; omega))
        rcases hh with hh | hh
        · exact ⟨.inr r,by simp [bag,step p r he hh],own r⟩
        · exact ⟨.inr p,own p,by simp [bag,step r p he.symm hh]⟩)
    (by
      intro v p hv
      have hv' := (old_mem v p).mp hv
      by_cases hz : p.2.val=0
      · have hp : A.parent p = .inl (owner p.1.1) := by simp [A,hz]
        rw [hp,graftBag_inl_inl]
        rcases hv' with rfl | ⟨a,rfl⟩
        · exact (D.inl_mem_apexBag _ _).mpr (ho _)
        · exact D.inr_mem_apexBag _ _
      · simp only [A,hz,↓reduceDIte,graftBag_inr]
        apply (old_mem _ _).mpr
        exact hv')
    (by intro r p p' hp hn hp' hn'; exact (top r p hp hn).symm.trans (top r p' hp' hn'))
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
    (hn : 5 ≤ n) {w : ℕ} (hw : HasWidth F w) :
    HasWidth (source F L) (max (w+2) 4) := by
  classical
  obtain ⟨d,B,T,D,hw⟩ := aug_width (n := n) F hw
  choose owner hs ht using fun l : Link F L => D.edge_cover (link_adj_aug F L l)
  have h := width_linked_of_bags D (base m n) (base_le_aug F)
    (fun l : Link F L => src l.val) (fun l => dst l.val) (n-3) (max (w+2) 4)
    (by omega) hw owner hs ht
  exact h.mono (by omega)

end TreewidthHom.OddCycle.ListReduction
