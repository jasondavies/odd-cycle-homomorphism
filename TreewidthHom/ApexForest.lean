module

public import TreewidthHom.Width
public import TreewidthHom.GraftDecomposition
public import TreewidthHom.IntervalDecomposition
public import TreewidthHom.DecompositionMaps

@[expose] public section

/-!
# Width from a small set of hubs whose removal leaves a forest

If the vertices outside a finite set of hubs carry well-founded parent pointers
covering every edge between two of them, the graph has a tree decomposition of
width at most the number of hubs plus one.
-/
namespace TreewidthHom
open SimpleGraph

namespace Decomposition
variable {V W B : Type*} [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {T : SimpleGraph B}

/-- Restrict a decomposition along an injective map from another graph. -/
noncomputable def comap (D : Decomposition G T) (H : SimpleGraph W) (ι : W → V)
    (hι : Function.Injective ι) (h : ∀ {u v}, H.Adj u v → G.Adj (ι u) (ι v)) :
    Decomposition H T where
  tree := D.tree
  bag b := (D.bag b).preimage ι hι.injOn
  vertex_cover v := by
    obtain ⟨b,hb⟩ := D.vertex_cover (ι v)
    exact ⟨b,by simpa using hb⟩
  edge_cover := by
    intro u v huv
    obtain ⟨b,hu,hv⟩ := D.edge_cover (h huv)
    exact ⟨b,by simpa using hu,by simpa using hv⟩
  running := by
    intro v a b ha hb
    obtain ⟨p,hp⟩ := D.running (ι v) a b (by simpa using ha) (by simpa using hb)
    exact ⟨p,fun c hc => by simpa using hp c hc⟩

theorem comap_card (D : Decomposition G T) (H : SimpleGraph W) (ι : W → V)
    (hι : Function.Injective ι) (h : ∀ {u v}, H.Adj u v → G.Adj (ι u) (ι v)) (b : B) :
    ((D.comap H ι hι h).bag b).card ≤ (D.bag b).card := by
  change ((D.bag b).preimage ι hι.injOn).card ≤ _
  exact Finset.card_le_card_of_injOn ι (fun x hx => by simpa using hx) hι.injOn

end Decomposition

/-- Hubs plus a forest: width at most the number of hubs plus one. -/
theorem hasWidth_of_apex_forest {V : Type} (G : SimpleGraph V) (hub : V → Prop)
    [Fintype {v // hub v}]
    (parent : {v // ¬ hub v} → Option {v // ¬ hub v}) (height : {v // ¬ hub v} → ℕ)
    (hdec : ∀ p q, parent p = some q → height q < height p)
    (hedge : ∀ p q : {v // ¬ hub v}, G.Adj p.val q.val → parent p = some q ∨ parent q = some p) :
    HasWidth G (Fintype.card {v // hub v} + 1) := by
  classical
  let P := {v // ¬ hub v}
  let A := {v // hub v}
  let F : Graft Unit P :=
    { parent := fun p => (parent p).elim (.inl ()) .inr
      height := height
      decreases := by
        intro p q h
        cases hp : parent p with
        | none => simp [hp] at h
        | some r =>
          have hr : r = q := by simpa [hp] using h
          subst hr
          exact hdec p r hp }
  let D0 : Decomposition (⊥ : SimpleGraph Unit) (⊥ : SimpleGraph Unit) :=
    { tree := IsTree.of_subsingleton
      bag := fun _ => Finset.univ
      vertex_cover := fun _ => ⟨(),Finset.mem_univ _⟩
      edge_cover := fun _ => ⟨(),Finset.mem_univ _,Finset.mem_univ _⟩
      running := by
        intro v a b ha hb
        have he : a = b := Subsingleton.elim _ _
        subst b
        exact ⟨.nil,fun _ _ => Finset.mem_univ _⟩ }
  let D1 := F.forestDecomposition D0 (fun _ => ()) (fun _ => Finset.mem_univ _)
  have hw1 : ∀ b, (D1.bag b).card ≤ 1+1 :=
    F.forest_width D0 (fun _ => ()) (fun _ => Finset.mem_univ _) (k := 0)
      (fun _ => by change (Finset.univ : Finset Unit).card ≤ 0+1; simp)
  let ι : V → (Unit ⊕ P) ⊕ A := fun v =>
    if h : hub v then .inr ⟨v,h⟩ else .inl (.inr ⟨v,h⟩)
  have hι : Function.Injective ι := by
    intro x y hxy
    by_cases hx : hub x <;> by_cases hy : hub y <;> simp [ι,hx,hy] at hxy
    · exact congrArg Subtype.val hxy
    · exact congrArg Subtype.val hxy
  let H' : SimpleGraph ((Unit ⊕ P) ⊕ A) :=
    { Adj := fun a b => ∃ x y, G.Adj x y ∧ ι x = a ∧ ι y = b
      symm := ⟨fun _ _ ⟨x,y,h,hx,hy⟩ => ⟨y,x,G.adj_symm h,hy,hx⟩⟩
      loopless := ⟨fun _ ⟨x,y,h,hx,hy⟩ => G.ne_of_adj h (hι (hx.trans hy.symm))⟩ }
  have hbase : ∀ {u v : Unit ⊕ P}, H'.Adj (.inl u) (.inl v) → (F.graph ⊥).Adj u v := by
    intro u v h
    obtain ⟨x,y,hxy,hx,hy⟩ := h
    by_cases hhx : hub x
    · simp [ι,hhx] at hx
    · by_cases hhy : hub y
      · simp [ι,hhy] at hy
      · simp only [ι,hhx,hhy,↓reduceDIte,Sum.inl.injEq] at hx hy
        subst hx; subst hy
        rcases hedge ⟨x,hhx⟩ ⟨y,hhy⟩ hxy with hp | hp
        · exact Or.inl (by simp [F,hp])
        · exact Or.inr (by simp [F,hp])
  let D2 := D1.addApices H' hbase
  let D3 := D2.comap G ι hι (fun {u v} h => ⟨u,v,h,rfl,rfl⟩)
  refine ⟨inferInstance,_,_,D3,fun b => ?_⟩
  have h3 : (D3.bag b).card ≤ (D1.apexBag (A := A) b).card :=
    D2.comap_card G ι hι (fun {u v} h => ⟨u,v,h,rfl,rfl⟩) b
  have h2 : (D1.apexBag (A := A) b).card ≤ (D1.bag b).card + Fintype.card {v // hub v} :=
    D1.apexBag_card (A := A) b
  have h1 := hw1 b
  omega

/-- Under the same hypotheses, deleting the hubs leaves an acyclic graph: the hubs
form a feedback vertex set. -/
theorem acyclic_of_apex_forest {V : Type} (G : SimpleGraph V) (hub : V → Prop)
    (parent : {v // ¬ hub v} → Option {v // ¬ hub v}) (height : {v // ¬ hub v} → ℕ)
    (hdec : ∀ p q, parent p = some q → height q < height p)
    (hedge : ∀ p q : {v // ¬ hub v}, G.Adj p.val q.val → parent p = some q ∨ parent q = some p) :
    (G.induce {v | ¬ hub v}).IsAcyclic := by
  classical
  let F : Graft Unit {v // ¬ hub v} :=
    { parent := fun p => (parent p).elim (.inl ()) .inr
      height := height
      decreases := by
        intro p q h
        cases hp : parent p with
        | none => simp [hp] at h
        | some r =>
          have hr : r = q := by simpa [hp] using h
          subst hr
          exact hdec p r hp }
  let f : G.induce {v | ¬ hub v} →g F.graph (⊥ : SimpleGraph Unit) :=
    { toFun := fun v => Sum.inr v
      map_rel' := by
        intro u v h
        rcases hedge u v h with hp | hp
        · exact Or.inl (by simp [F,hp])
        · exact Or.inr (by simp [F,hp]) }
  have hinj : Function.Injective f := fun u v h => Sum.inr.inj h
  have hF : (F.graph (⊥ : SimpleGraph Unit)).IsAcyclic :=
    F.acyclic ⊥ (IsTree.of_subsingleton (G := (⊥ : SimpleGraph Unit))).isAcyclic
  intro v p hp
  exact hF (p.map f) (hp.map hinj)

/-- Phases along a path. Retained vertices occupy intervals of phases, with at most
`m` of them per phase. Every other vertex belongs to one phase, sees only retained
vertices of that phase, and hangs in a forest of parent pointers. Then the width is
at most `m+1`. -/
theorem hasWidth_of_phased_forest {V : Type} (G : SimpleGraph V) (ret : V → Prop) (R m : ℕ)
    (S : Fin (R+1) → Finset {v // ret v})
    (hS : ∀ t, (S t).card ≤ m)
    (hcover : ∀ v, ∃ t, v ∈ S t)
    (hconvex : ∀ v a b c, a ≤ c → c ≤ b → v ∈ S a → v ∈ S b → v ∈ S c)
    (hret : ∀ u v : {v // ret v}, G.Adj u.val v.val → ∃ t, u ∈ S t ∧ v ∈ S t)
    (phase : {v // ¬ ret v} → Fin (R+1))
    (parent : {v // ¬ ret v} → Option {v // ¬ ret v}) (height : {v // ¬ ret v} → ℕ)
    (hdec : ∀ p q, parent p = some q → height q < height p)
    (hphase : ∀ p q, parent p = some q → phase q = phase p)
    (hmixed : ∀ (p : {v // ¬ ret v}) (v : {v // ret v}), G.Adj p.val v.val → v ∈ S (phase p))
    (hedge : ∀ p q : {v // ¬ ret v}, G.Adj p.val q.val → parent p = some q ∨ parent q = some p) :
    HasWidth G (m+1) := by
  classical
  let A := {v // ret v}
  let P := {v // ¬ ret v}
  let e : A ⊕ P ≃ V := Equiv.sumCompl ret
  let H : SimpleGraph (A ⊕ P) := G.comap e
  let G0 : SimpleGraph A := G.comap Subtype.val
  let D0 : Decomposition G0 (pathGraph (R+1)) :=
    intervalDecomposition G0 R S hcover (fun {u v} h => hret u v h) hconvex
  let F : Graft (Fin (R+1)) P :=
    { parent := fun p => (parent p).elim (.inl (phase p)) .inr
      height := height
      decreases := by
        intro p q h
        cases hp : parent p with
        | none => simp [hp] at h
        | some r =>
          have hr : r = q := by simpa [hp] using h
          subst hr
          exact hdec p r hp }
  let newBag : P → Finset (A ⊕ P) := fun p =>
    (S (phase p)).map ⟨Sum.inl,Sum.inl_injective⟩ ∪
      insert (Sum.inr p) ((parent p).elim ∅ (fun q => {Sum.inr q}))
  have mem_inl : ∀ (v : A) (p : P), Sum.inl v ∈ newBag p ↔ v ∈ S (phase p) := by
    intro v p
    cases hp : parent p <;> simp [newBag,hp]
  have mem_inr : ∀ (q p : P), Sum.inr q ∈ newBag p ↔ q = p ∨ parent p = some q := by
    intro q p
    cases hp : parent p <;> simp [newBag,hp,eq_comm]
  have bag0 : ∀ t, D0.bag t = S t := fun _ => rfl
  have key : ∀ q p : P, Sum.inr q ∈ newBag p →
      Sum.inr q ∉ graftBag D0 newBag (F.parent p) → q = p := by
    intro q p hm hn
    rcases (mem_inr q p).mp hm with h | h
    · exact h
    · refine False.elim (hn ?_)
      have hF : F.parent p = Sum.inr q := by simp [F,h]
      rw [hF,graftBag_inr]
      exact (mem_inr q q).mpr (Or.inl rfl)
  let D1 := F.extend D0 H newBag
    (fun q => ⟨q,(mem_inr q q).mpr (Or.inl rfl)⟩)
    (by
      rintro (a | p) (b | q) h
      · obtain ⟨t,hu,hv⟩ := hret a b h
        exact ⟨.inl t,(graftBag_inl_inl D0 newBag a t).mpr hu,(graftBag_inl_inl D0 newBag b t).mpr hv⟩
      · have hm := hmixed q a (G.adj_symm h)
        exact ⟨.inr q,(mem_inl a q).mpr hm,(mem_inr q q).mpr (Or.inl rfl)⟩
      · have hm := hmixed p b h
        exact ⟨.inr p,(mem_inr p p).mpr (Or.inl rfl),(mem_inl b p).mpr hm⟩
      · rcases hedge p q h with hp | hq
        · exact ⟨.inr p,(mem_inr p p).mpr (Or.inl rfl),(mem_inr q p).mpr (Or.inr hp)⟩
        · exact ⟨.inr q,(mem_inr p q).mpr (Or.inr hq),(mem_inr q q).mpr (Or.inl rfl)⟩)
    (by
      intro v p hv
      have hv' := (mem_inl v p).mp hv
      cases hp : parent p with
      | none =>
        have hF : F.parent p = Sum.inl (phase p) := by simp [F,hp]
        rw [hF,graftBag_inl_inl]
        exact hv'
      | some q =>
        have hF : F.parent p = Sum.inr q := by simp [F,hp]
        rw [hF,graftBag_inr,mem_inl,hphase p q hp]
        exact hv')
    (by
      intro q p p' hm hn hm' hn'
      exact (key q p hm hn).symm.trans (key q p' hm' hn'))
  have he : ∀ u v, G.Adj (e u) (e v) → H.Adj u v := fun _ _ h => h
  refine ⟨inferInstance,_,_,D1.mapEquiv e he,fun b => ?_⟩
  rw [Decomposition.mapEquiv_card]
  change (graftBag D0 newBag b).card ≤ _
  rcases b with t | p
  · have := hS t
    simp only [graftBag,Finset.card_map,bag0]
    omega
  · have h1 : ((S (phase p)).map ⟨Sum.inl,Sum.inl_injective⟩ : Finset (A ⊕ P)).card ≤ m := by
      rw [Finset.card_map]; exact hS _
    have h2 : (insert (Sum.inr p) ((parent p).elim ∅ (fun q => {Sum.inr q})) :
        Finset (A ⊕ P)).card ≤ 2 := by
      cases parent p with
      | none => simp
      | some q => exact Finset.card_le_two
    have h3 : (newBag p).card ≤
        ((S (phase p)).map ⟨Sum.inl,Sum.inl_injective⟩ : Finset (A ⊕ P)).card +
        (insert (Sum.inr p) ((parent p).elim ∅ (fun q => {Sum.inr q})) : Finset (A ⊕ P)).card :=
      Finset.card_union_le _ _
    change (newBag p).card ≤ _
    omega

end TreewidthHom
