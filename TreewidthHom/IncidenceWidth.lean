module

public import TreewidthHom.GraftDecomposition
public import TreewidthHom.LCSQueryWidth
public import TreewidthHom.ColorWidth

@[expose] public section

namespace TreewidthHom.Relational
open SimpleGraph
variable {R : Type} {arity : R → ℕ} {V B : Type*}
variable [DecidableEq V] (A : Relational R arity V)

abbrev Private := Σ f : A.Fact, Unit ⊕ Fin (arity f.1)

/-- Bag indices for one fact: a root bag and one child bag per argument position. -/
abbrev Node := Σ f : A.Fact, Option (Fin (arity f.1))

noncomputable def args (f : A.Fact) : Finset V := Finset.univ.image f.2.val

/-- The fact's root bag hangs below an old bag; its port bags hang below the root. -/
def factGraft (parent : A.Fact → B) : Graft B A.Node where
  parent p := match p.2 with
    | none => .inl (parent p.1)
    | some _ => .inr ⟨p.1,none⟩
  height p := match p.2 with
    | none => 0
    | some _ => 1
  decreases := by
    rintro ⟨f,_ | i⟩ q h
    · cases h
    · cases Sum.inr.inj h
      exact Nat.zero_lt_one

/-- Root bag: the arguments and the tuple vertex. Child bag: one argument, the
tuple vertex and the corresponding port. -/
noncomputable def nodeBag : A.Node → Finset (V ⊕ A.Private) := by
  classical
  exact fun p => match p with
    | ⟨f,none⟩ => insert (Sum.inr ⟨f,.inl ()⟩) ((A.args f).map ⟨Sum.inl,Sum.inl_injective⟩)
    | ⟨f,some i⟩ => {Sum.inl (f.2.val i),Sum.inr ⟨f,.inl ()⟩,Sum.inr ⟨f,.inr i⟩}

/-- The topmost bag containing a private incidence vertex. -/
def topNode : A.Private → A.Node
  | ⟨f,.inl _⟩ => ⟨f,none⟩
  | ⟨f,.inr i⟩ => ⟨f,some i⟩

@[simp] theorem base_root (v : V) (f : A.Fact) :
    Sum.inl v ∈ A.nodeBag ⟨f,none⟩ ↔ v ∈ A.args f := by
  classical
  simp [nodeBag]

@[simp] theorem base_child (v : V) (f : A.Fact) (i : Fin (arity f.1)) :
    Sum.inl v ∈ A.nodeBag ⟨f,some i⟩ ↔ v = f.2.val i := by
  classical
  simp [nodeBag]

@[simp] theorem private_root (p : A.Private) (f : A.Fact) :
    Sum.inr p ∈ A.nodeBag ⟨f,none⟩ ↔ p = ⟨f,.inl ()⟩ := by
  classical
  simp [nodeBag]

@[simp] theorem private_child (p : A.Private) (f : A.Fact) (i : Fin (arity f.1)) :
    Sum.inr p ∈ A.nodeBag ⟨f,some i⟩ ↔ p = ⟨f,.inl ()⟩ ∨ p = ⟨f,.inr i⟩ := by
  classical
  simp [nodeBag]

theorem mem_topNode (p : A.Private) : Sum.inr p ∈ A.nodeBag (A.topNode p) := by
  rcases p with ⟨f,u | i⟩
  · cases u
    exact (A.private_root _ f).mpr rfl
  · exact (A.private_child _ f i).mpr (Or.inr rfl)

theorem nodeBag_card (p : A.Node) (ha : arity p.1.1 ≤ 2) : (A.nodeBag p).card ≤ 2+1 := by
  classical
  rcases p with ⟨f,_ | i⟩
  · have h1 : (A.args f).card ≤ arity f.1 := Finset.card_image_le.trans (by simp)
    have h2 := Finset.card_insert_le (Sum.inr ⟨f,.inl ()⟩ : V ⊕ A.Private)
      ((A.args f).map ⟨Sum.inl,Sum.inl_injective⟩)
    simp only [Finset.card_map] at h2
    change (A.nodeBag ⟨f,none⟩).card ≤ _
    unfold nodeBag
    dsimp only at ha ⊢
    omega
  · exact Finset.card_le_three

theorem incidence_width [DecidableEq A.Vertex] {G : SimpleGraph V} {T : SimpleGraph B}
    (D : Decomposition G T) (ha : ∀ r, arity r ≤ 2)
    (hf : ∀ f : A.Fact, ∃ b, A.args f ⊆ D.bag b)
    {k : ℕ} (hw : ∀ b, (D.bag b).card ≤ k+1) :
    ∃ T' : SimpleGraph (B ⊕ A.Node), ∃ D' : Decomposition A.typedDag.base.underlying T',
      ∀ b, (D'.bag b).card ≤ max k 2+1 := by
  classical
  choose parent hp using hf
  let F := A.factGraft parent
  let H := A.typedDag.base.underlying.comap (A.vertexEquiv).symm
  have hedges : ∀ {u v}, H.Adj u v → ∃ b,
      u ∈ graftBag D A.nodeBag b ∧ v ∈ graftBag D A.nodeBag b := by
    have one : ∀ {x y : A.Vertex}, A.Edge x y → ∃ p,
        A.vertexEquiv x ∈ A.nodeBag p ∧ A.vertexEquiv y ∈ A.nodeBag p := by
      intro x y h
      cases h with
      | first f i => exact ⟨⟨f,some i⟩,by simp [vertexEquiv],by simp [vertexEquiv]⟩
      | second f i => exact ⟨⟨f,some i⟩,by simp [vertexEquiv],by simp [vertexEquiv]⟩
    intro u v h
    change A.Edge _ _ ∨ A.Edge _ _ at h
    rcases h with h | h
    · obtain ⟨p,h1,h2⟩ := one h
      exact ⟨.inr p,by simpa using h1,by simpa using h2⟩
    · obtain ⟨p,h1,h2⟩ := one h
      exact ⟨.inr p,by simpa using h2,by simpa using h1⟩
  have key : ∀ (q : A.Private) (p : A.Node), Sum.inr q ∈ A.nodeBag p →
      Sum.inr q ∉ graftBag D A.nodeBag (F.parent p) → p = A.topNode q := by
    rintro q ⟨f,_ | i⟩ hm hn
    · have hq := (A.private_root q f).mp hm
      subst q
      rfl
    · rcases (A.private_child q f i).mp hm with hq | hq
      · subst q
        exact False.elim (hn ((A.private_root _ f).mpr rfl))
      · subst q
        rfl
  let D0 := F.extend D H A.nodeBag
    (fun q => ⟨A.topNode q,A.mem_topNode q⟩) hedges
    (by
      rintro v ⟨f,_ | i⟩ hv
      · have hv' := (A.base_root v f).mp hv
        exact (graftBag_inl_inl D A.nodeBag v (parent f)).mpr (hp f hv')
      · have hv' := (A.base_child v f i).mp hv
        subst v
        change Sum.inl (f.2.val i) ∈ A.nodeBag ⟨f,none⟩
        exact (A.base_root _ f).mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    (by
      intro q p p' hm hn hm' hn'
      exact (key q p hm hn).trans (key q p' hm' hn').symm)
  have he : ∀ u v, A.typedDag.base.underlying.Adj (A.vertexEquiv.symm u) (A.vertexEquiv.symm v) → H.Adj u v :=
    fun _ _ h => h
  refine ⟨_,D0.mapEquiv A.vertexEquiv.symm he,?_⟩
  intro b
  rw [Decomposition.mapEquiv_card]
  exact graftBag_card D A.nodeBag hw (fun p => A.nodeBag_card p (ha p.1.1)) b

end TreewidthHom.Relational

namespace TreewidthHom.UnaryBinary
open SimpleGraph
variable {V B : Type*} [DecidableEq V] (A : UnaryBinary V)

/-- Each unary or binary fact's arguments fit in a Gaifman bag. -/
theorem fact_bag {T : SimpleGraph B} (D : Decomposition A.gaifman T)
    (f : A.asRelational.Fact) : ∃ b, A.asRelational.args f ⊆ D.bag b := by
  classical
  apply D.small_clique_bag
  · have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin (Relational.schemaArity f.1)))) (f := f.2.val)
    have ha : Relational.schemaArity f.1 ≤ 2 := by unfold Relational.schemaArity; split <;> omega
    simp only [Finset.card_univ,Fintype.card_fin] at h
    exact h.trans ha
  · intro u hu v hv hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    have hf := f.2.prop
    by_cases hr : f.1 = 0
    · have hi : i.val = 0 := by have := i.isLt; simp [Relational.schemaArity,hr] at this; omega
      have hj : j.val = 0 := by have := j.isLt; simp [Relational.schemaArity,hr] at this; omega
      exact False.elim (hne (congrArg f.2.val (Fin.ext (hi.trans hj.symm))))
    · have hi : i.val < 2 := by simpa [Relational.schemaArity,hr] using i.isLt
      have hj : j.val < 2 := by simpa [Relational.schemaArity,hr] using j.isLt
      have hij : i.val ≠ j.val := fun he => hne (congrArg f.2.val (Fin.ext he))
      simp only [asRelational,dite_eq_right hr] at hf
      refine ⟨hne,⟨f.1.val-1,by have := f.1.isLt; omega⟩,?_⟩
      rcases (show (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) by omega) with h | h
      · left
        have he1 : i = ⟨0,by simp [Relational.schemaArity,hr]⟩ := Fin.ext h.1
        have he2 : j = ⟨1,by simp [Relational.schemaArity,hr]⟩ := Fin.ext h.2
        simpa [he1,he2] using hf
      · right
        have he1 : i = ⟨1,by simp [Relational.schemaArity,hr]⟩ := Fin.ext h.1
        have he2 : j = ⟨0,by simp [Relational.schemaArity,hr]⟩ := Fin.ext h.2
        simpa [he1,he2] using hf

end TreewidthHom.UnaryBinary
