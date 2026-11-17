module

public import TreewidthHom.ListReduction
public import TreewidthHom.ForestOrientation
public import TreewidthHom.ApexForest

@[expose] public section

namespace TreewidthHom.OddCycle.ListReduction
open SimpleGraph Reference
variable {m n : ℕ} [Fact (1 < n)]

def removed {F : SimpleGraph (Fin m)} {L : Fin m → Finset (ZMod n)}
    (S : Finset (Fin m)) : SourceVertex F L → Prop
  | .inl (.inl (.inl _)) => True
  | .inl (.inr v) => v ∈ S
  | _ => False

section
variable (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n)) (S : Finset (Fin m))
variable (O : ForestOrientation (F.induce {v | v ∉ S}))

noncomputable def oldRank (v : Fin m) : ℕ :=
  if h : v ∉ S then O.rank ⟨v,h⟩ else 0

noncomputable def oldParent (v : Fin m) : Option (Fin m) :=
  if h : v ∉ S then (O.parent ⟨v,h⟩).map Subtype.val else none

theorem oldParent_spec {v u : Fin m} (h : oldParent F S O v=some u) :
    v ∉ S ∧ u ∉ S ∧ F.Adj v u ∧ oldRank F S O v=oldRank F S O u+1 := by
  classical
  unfold oldParent at h
  split_ifs at h with hv
  obtain ⟨u',hp,hu⟩ := Option.map_eq_some_iff.mp h
  subst u
  have hh := O.parent_spec _ _ hp
  have hu' : u'.val ∉ S := u'.prop
  exact ⟨hv,hu',hh.1,by rw [oldRank,dite_eq_left hv,oldRank,dite_eq_left hu']; exact hh.2⟩

theorem oldParent_edge {v u : Fin m} (hv : v ∉ S) (hu : u ∉ S) (h : F.Adj v u) :
    oldParent F S O v=some u ∨ oldParent F S O u=some v := by
  classical
  rcases O.edge ⟨v,hv⟩ ⟨u,hu⟩ h with hh | hh
  · left; simp [oldParent,hv,hh]
  · right; simp [oldParent,hu,hh]

noncomputable def edgeLink (u v : Fin m) (h : F.Adj u v) : Link F L :=
  if huv : u<v then ⟨.inr (u,v),huv,h⟩ else
    ⟨.inr (v,u),lt_of_le_of_ne (le_of_not_gt huv) h.ne.symm,h.symm⟩

noncomputable def towardStart (u v : Fin m) : Bool :=
  decide (u ∉ S ∧ (v ∈ S ∨ oldRank F S O u < oldRank F S O v))

def center (d : ZMod n) : ℕ := d.val-2

noncomputable def ceiling : ℕ := 1+∑ v : Fin m, oldRank F S O v*(n-2)

omit [Fact (1 < n)] in
theorem hub_below (v : Fin m) : oldRank F S O v*(n-2) < ceiling (n := n) F S O := by
  classical
  have hh := Finset.single_le_sum (s := Finset.univ) (f := fun v : Fin m => oldRank F S O v*(n-2))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  dsimp [ceiling]; omega

noncomputable def height : SourceVertex F L → ℕ
  | .inl (.inl (.inl _)) => 0
  | .inl (.inr v) => oldRank F S O v*(n-2)
  | .inl (.inl (.inr ((_,d),c))) => ceiling (n := n) F S O+(n-3)+Nat.dist c.val (center d)+1
  | .inr (⟨.inl _,_⟩,c) => ceiling (n := n) F S O+(n-3-c.val)
  | .inr (⟨.inr (u,v),_⟩,c) =>
      if towardStart F S O u v then oldRank F S O u*(n-2)+c.val+1
      else oldRank F S O v*(n-2)+(n-3-c.val)

noncomputable def parent (hn : 5 ≤ n) : SourceVertex F L → Option (SourceVertex F L)
  | .inl (.inl (.inl _)) => none
  | .inl (.inr v) =>
      match h : oldParent F S O v with
      | none => none
      | some u =>
        let l := edgeLink F L v u (oldParent_spec F S O h).2.2.1
        some (.inr (l,if v<u then ⟨0,by omega⟩ else ⟨n-4,by omega⟩))
  | .inl (.inl (.inr ((v,d),c))) =>
      if h : c.val < center d then
        some (.inl (.inl (.inr ((v,d),⟨c.val+1,by have := ZMod.val_lt d; dsimp [center] at h; omega⟩))))
      else if h' : center d < c.val then
        some (.inl (.inl (.inr ((v,d),⟨c.val-1,by have := c.isLt; omega⟩))))
      else if hd : d ∉ L v ∧ 2 ≤ d.val then
        some (.inr (⟨.inl (v,d),hd.1⟩,⟨0,by omega⟩))
      else none
  | .inr (l,c) => match l with
    | ⟨.inl (v,d),_⟩ =>
        if h : c.val+1 < n-3 then some (.inr (⟨.inl (v,d),by assumption⟩,⟨c.val+1,h⟩))
        else if hv : v ∉ S then some (.inl (.inr v)) else none
    | ⟨.inr (u,v),_⟩ =>
        if towardStart F S O u v then
          if h : c.val=0 then if hu : u ∉ S then some (.inl (.inr u)) else none
          else some (.inr (⟨.inr (u,v),by assumption⟩,⟨c.val-1,by have := c.isLt; omega⟩))
        else if h : c.val+1 < n-3 then some (.inr (⟨.inr (u,v),by assumption⟩,⟨c.val+1,h⟩))
        else if hv : v ∉ S then some (.inl (.inr v)) else none

theorem parent_hub (hn : 5 ≤ n) {v u : Fin m} (h : oldParent F S O v=some u) :
    parent F L S O hn (.inl (.inr v)) =
      some (.inr (edgeLink F L v u (oldParent_spec F S O h).2.2.1,
        if v<u then ⟨0,by omega⟩ else ⟨n-4,by omega⟩)) := by
  classical
  simp only [parent]
  split
  · rename_i hp
    simp [h] at hp
  · rename_i u' hp
    have he : u' = u := Option.some.inj (hp.symm.trans h)
    subst u'
    rfl

theorem away_start {u v : Fin m} (h : F.Adj u v) (hu : u ∉ S)
    (hf : towardStart F S O u v=false) : oldParent F S O u=some v := by
  classical
  have hn : ¬ (u ∉ S ∧ (v ∈ S ∨ oldRank F S O u < oldRank F S O v)) := by
    simpa [towardStart] using hf
  have hv : v ∉ S := fun hh => hn ⟨hu,Or.inl hh⟩
  rcases oldParent_edge F S O hu hv h with hh | hh
  · exact hh
  · have hs := (oldParent_spec F S O hh).2.2.2
    exact False.elim (hn ⟨hu,Or.inr (by omega)⟩)

theorem away_end {u v : Fin m} (h : F.Adj u v) (hv : v ∉ S)
    (hf : towardStart F S O u v=true) : oldParent F S O v=some u := by
  classical
  have hh : u ∉ S ∧ (v ∈ S ∨ oldRank F S O u < oldRank F S O v) := by
    simpa [towardStart] using hf
  have hr := hh.2.resolve_left hv
  rcases oldParent_edge F S O hh.1 hv h with hp | hp
  · have hs := (oldParent_spec F S O hp).2.2.2
    omega
  · exact hp

theorem parent_cases (hn : 5 ≤ n) {x y : SourceVertex F L}
    (h : parent F L S O hn x=some y) :
    ¬ removed S y ∧ height F L S O y < height F L S O x := by
  classical
  rcases x with ((a | ⟨⟨v,d⟩,c⟩) | v) | ⟨⟨(⟨v,d⟩ | ⟨u,v⟩),hl⟩,c⟩
  · simp [parent] at h
  · -- Private reference vertices move towards their attachment coordinate.
    simp only [parent] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h
    all_goals subst y; simp_all [removed, height, Nat.dist]
    all_goals omega
  · cases hu : oldParent F S O v with
    | none =>
      simp only [parent] at h
      split at h <;> simp_all
    | some u =>
      rw [parent_hub F L S O hn hu] at h
      have he := Option.some.inj h
      subst y
      refine ⟨id,?_⟩
      obtain ⟨hv,hu',hvu,hr⟩ := oldParent_spec F S O hu
      have heq : (oldRank F S O u+1)*(n-2) = oldRank F S O u*(n-2)+(n-2) := by ring
      by_cases hvu' : v<u
      · have hfalse : towardStart F S O v u=false := by simp [towardStart,hv,hu']; omega
        simp only [edgeLink,dite_eq_left hvu',height,hfalse,Bool.false_eq_true,↓reduceIte]
        rw [hr,heq]
        omega
      · have htrue : towardStart F S O u v=true := by simp [towardStart,hv,hu']; omega
        simp only [edgeLink,dite_eq_right hvu',height,htrue,↓reduceIte]
        rw [hr,heq]
        omega
  · -- Domain links move towards their hub, below the reference vertices.
    have := hub_below (n := n) F S O v
    have := c.isLt
    simp only [parent] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h
    all_goals subst y; simp_all [removed, height]
    all_goals omega
  · -- Original-edge links move towards the lower surviving endpoint.
    have := c.isLt
    simp only [parent] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h
    all_goals subst y; simp_all [removed, height]
    all_goals omega

theorem parent_private_edge (hn : 5 ≤ n) {p r : Private m n}
    (h : (base m n).Adj (.inl (.inr p)) (.inl (.inr r))) :
    parent F L S O hn (.inl (.inl (.inr p)))=some (.inl (.inl (.inr r))) ∨
    parent F L S O hn (.inl (.inl (.inr r)))=some (.inl (.inl (.inr p))) := by
  classical
  have step : ∀ (i : Copies m n) (a b : Fin (n-2)), b.val=a.val+1 →
      parent F L S O hn (.inl (.inl (.inr (i,a))))=some (.inl (.inl (.inr (i,b)))) ∨
      parent F L S O hn (.inl (.inl (.inr (i,b))))=some (.inl (.inl (.inr (i,a)))) := by
    rintro ⟨v,d⟩ a b hab
    by_cases ha : a.val < center d
    · left
      simp only [parent,ha,↓reduceDIte,Option.some.injEq,Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq,true_and]
      exact Fin.ext (by dsimp only; omega)
    · right
      have hb : ¬ b.val < center d := by omega
      have hb' : center d < b.val := by omega
      simp only [parent,hb,hb',↓reduceDIte,Option.some.injEq,Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq,true_and]
      exact Fin.ext (by dsimp only; omega)
  obtain ⟨he,hh⟩ := private_adj h
  rcases p with ⟨i,a⟩; rcases r with ⟨j,b⟩
  dsimp only at he hh
  subst j
  rcases hh with hh | hh
  · exact step i a b hh
  · exact (step i b a hh).symm

theorem parent_mixed_edge (hn : 5 ≤ n) (x : BaseVertex m n) (l : Link F L) (c : Fin (n-3))
    (hx : ¬ removed (F := F) (L := L) S (.inl x))
    (h : (c.val=0 ∧ x=src l.val) ∨ (c.val+1=n-3 ∧ x=dst l.val)) :
    parent F L S O hn (.inl x)=some (.inr (l,c)) ∨
    parent F L S O hn (.inr (l,c))=some (.inl x) := by
  classical
  rcases h with ⟨hc,rfl⟩ | ⟨hc,rfl⟩
  · rcases l with ⟨(⟨v,d⟩ | ⟨u,v⟩),hl⟩
    · rcases he : ref (v,d) d with a | ⟨i,e⟩
      · exact False.elim (hx (by change removed S (.inl (.inl (ref (v,d) d))); rw [he]; trivial))
      · obtain ⟨hi,hd⟩ := ref_private he
        subst i
        left
        change parent F L S O hn (.inl (.inl (ref (v,d) d)))=some _
        rw [he]
        have hcenter : center d=e.val := by dsimp [center]; omega
        have hd' : d ∉ L v ∧ 2 ≤ d.val := ⟨hl,by omega⟩
        have hc0 : c=⟨0,by omega⟩ := Fin.ext hc
        simp [parent,hcenter,hd',hc0]
    · have hu : u ∉ S := hx
      cases hf : towardStart F S O u v
      · left
        have hp := away_start F S O hl.2 hu hf
        rw [show src (Sum.inr (u,v) : Code m n)=Sum.inr u from rfl,parent_hub F L S O hn hp]
        simp only [edgeLink,dite_eq_left hl.1,ite_eq_left hl.1,Option.some.injEq,Sum.inr.injEq,Prod.mk.injEq,true_and]
        exact Fin.ext (by change 0=c.val; omega)
      · right
        simp [parent,hf,hc,hu,src]
  · rcases l with ⟨(⟨v,d⟩ | ⟨u,v⟩),hl⟩
    · right
      have hv : v ∉ S := hx
      have hh : ¬ c.val+1<n-3 := by omega
      simp [parent,hh,hv,dst]
    · have hv : v ∉ S := hx
      cases hf : towardStart F S O u v
      · right
        have hh : ¬ c.val+1<n-3 := by omega
        simp [parent,hf,hh,hv,dst]
      · left
        have hp := away_end F S O hl.2 hv hf
        rw [show dst (Sum.inr (u,v) : Code m n)=Sum.inr v from rfl,parent_hub F L S O hn hp]
        have hnot : ¬ v<u := (not_lt_of_ge hl.1.le)
        simp only [edgeLink,dite_eq_right hnot,ite_eq_right hnot,Option.some.injEq,Sum.inr.injEq,Prod.mk.injEq,true_and]
        exact Fin.ext (by change n-4=c.val; omega)

theorem parent_inner_edge (hn : 5 ≤ n) (l : Link F L) (a b : Fin (n-3))
    (h : b.val=a.val+1) :
    parent F L S O hn (.inr (l,a))=some (.inr (l,b)) ∨
    parent F L S O hn (.inr (l,b))=some (.inr (l,a)) := by
  classical
  have ha : a.val+1<n-3 := by have := b.isLt; omega
  rcases l with ⟨(⟨v,d⟩ | ⟨u,v⟩),hl⟩
  · left
    simp [parent, ha, Fin.ext_iff, h]
  · cases hf : towardStart F S O u v
    · left
      simp [parent, hf, ha, Fin.ext_iff, h]
    · right
      simp [parent, hf, h]

theorem parent_edge (hn : 5 ≤ n) {x y : SourceVertex F L}
    (hx : ¬ removed S x) (hy : ¬ removed S y) (h : (source F L).Adj x y) :
    parent F L S O hn x=some y ∨ parent F L S O hn y=some x := by
  rcases x with x | ⟨l,a⟩ <;> rcases y with y | ⟨l',b⟩
  · rcases x with (u | p) | u <;> rcases y with (v | r) | v
    all_goals try exact False.elim (hx trivial)
    all_goals try exact False.elim (hy trivial)
    · exact parent_private_edge F L S O hn h
    all_goals obtain ⟨_,h | h⟩ := (fromRel_adj _ _ _).mp (show (base m n).Adj _ _ from h) <;> exact h.elim
  · exact parent_mixed_edge F L S O hn x l' b hx h
  · exact (parent_mixed_edge F L S O hn y l a hy h).symm
  · obtain ⟨he,hh⟩ : l=l' ∧ (b.val=a.val+1 ∨ a.val=b.val+1) := h
    subst l'
    rcases hh with hh | hh
    · exact parent_inner_edge F L S O hn l a b hh
    · exact (parent_inner_edge F L S O hn l b a hh).symm

end

/-- Deleting the original feedback vertices and the two shared reference vertices
leaves a forest. -/
theorem source_feedback (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    (S : Finset (Fin m)) (hn : 5 ≤ n) (hS : (F.induce {v | v ∉ S}).IsAcyclic) :
    ((source F L).induce {v | ¬ removed S v}).IsAcyclic := by
  classical
  obtain ⟨O⟩ := exists_forestOrientation _ hS
  let P := {v : SourceVertex F L // ¬ removed S v}
  let par : P → Option P := fun p =>
    (parent F L S O hn p.val).pmap (fun q hq => ⟨q,(parent_cases F L S O hn hq).1⟩)
      (fun q hq => hq)
  apply acyclic_of_apex_forest (source F L) (removed S) par (fun p => height F L S O p.val)
  · intro p q h
    have hh : parent F L S O hn p.val=some q.val := by
      cases he : parent F L S O hn p.val with
      | none => simp [par,he] at h
      | some r =>
        have hr : r=q.val := by simpa [par,he] using congrArg (Option.map Subtype.val) h
        simp [hr]
    exact (parent_cases F L S O hn hh).2
  · intro p q h
    rcases parent_edge F L S O hn p.prop q.prop h with hh | hh
    · left; simp [par,hh]
    · right; simp [par,hh]

omit [Fact (1 < n)] in
/-- The deleted set has exactly the original size plus two. -/
theorem removed_card (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n)) (S : Finset (Fin m)) :
    Nat.card {v : SourceVertex F L // removed S v} = S.card+2 := by
  classical
  let e : {v : SourceVertex F L // removed S v} ≃ (Fin 2 ⊕ {v // v ∈ S}) :=
    { toFun := fun x => match x with
        | ⟨.inl (.inl (.inl a)),_⟩ => .inl a
        | ⟨.inl (.inl (.inr _)),h⟩ => h.elim
        | ⟨.inl (.inr v),h⟩ => .inr ⟨v,h⟩
        | ⟨.inr _,h⟩ => h.elim
      invFun := fun x => match x with
        | .inl a => ⟨.inl (.inl (.inl a)),trivial⟩
        | .inr v => ⟨.inl (.inr v.val),v.prop⟩
      left_inv := by
        rintro ⟨(((a | p) | v) | l),h⟩
        · rfl
        · exact False.elim h
        · rfl
        · exact False.elim h
      right_inv := by rintro (a | v) <;> rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_fin,Fintype.card_coe]
  omega

end TreewidthHom.OddCycle.ListReduction
