module

public import TreewidthHom.ReductionWidth

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

end TreewidthHom
