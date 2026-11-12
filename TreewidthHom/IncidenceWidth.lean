module

public import TreewidthHom.LeafExtension
public import TreewidthHom.LCSQueryWidth
public import TreewidthHom.ColorWidth

@[expose] public section

namespace TreewidthHom.Relational
open SimpleGraph
variable {R : Type} {arity : R → ℕ} {V B : Type*}
variable [DecidableEq V] (A : Relational R arity V)

abbrev Private := Σ f : A.Fact, Unit ⊕ Fin (arity f.1)

noncomputable def args (f : A.Fact) : Finset V := Finset.univ.image f.2.val
noncomputable def piece (f : A.Fact) : Finset (V ⊕ A.Private) := by
  classical
  exact (A.args f).map ⟨Sum.inl,Sum.inl_injective⟩ ∪
    Finset.univ.image (fun s : Unit ⊕ Fin (arity f.1) => Sum.inr ⟨f,s⟩)

@[simp] theorem base_piece (v : V) (f : A.Fact) :
    Sum.inl v ∈ A.piece f ↔ v ∈ A.args f := by
  classical
  simp [piece]

@[simp] theorem private_piece (p : A.Private) (f : A.Fact) :
    Sum.inr p ∈ A.piece f ↔ f = p.1 := by
  classical
  simp only [piece,Finset.mem_union,Finset.mem_map,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro (⟨v,_,hv⟩ | ⟨s,hs⟩)
    · cases hv
    · exact congrArg Sigma.fst (Sum.inr.inj hs)
  · intro h
    rcases p with ⟨g,s⟩
    dsimp at h
    subst g
    exact Or.inr ⟨s,rfl⟩

theorem piece_card (f : A.Fact) (ha : arity f.1 ≤ 2) : (A.piece f).card ≤ 5 := by
  classical
  have h1 : (A.args f).card ≤ arity f.1 := Finset.card_image_le.trans (by simp)
  have h2 : (Finset.univ.image (fun s : Unit ⊕ Fin (arity f.1) => (Sum.inr ⟨f,s⟩ : V ⊕ A.Private))).card ≤ 1+arity f.1 :=
    Finset.card_image_le.trans (by simp)
  have h3 := Finset.card_union_le ((A.args f).map ⟨Sum.inl,Sum.inl_injective⟩)
    (Finset.univ.image (fun s : Unit ⊕ Fin (arity f.1) => (Sum.inr ⟨f,s⟩ : V ⊕ A.Private)))
  simp only [Finset.card_map] at h3
  change (A.piece f).card ≤ _ at h3
  omega

noncomputable def incidenceBag {G : SimpleGraph V} {T : SimpleGraph B}
    (D : Decomposition G T) : B ⊕ A.Fact → Finset (V ⊕ A.Private)
  | .inl b => (D.bag b).map ⟨Sum.inl,Sum.inl_injective⟩
  | .inr f => A.piece f

theorem incidence_width [DecidableEq A.Vertex] {G : SimpleGraph V} {T : SimpleGraph B}
    (D : Decomposition G T) (ha : ∀ r, arity r ≤ 2)
    (hf : ∀ f : A.Fact, ∃ b, A.args f ⊆ D.bag b)
    {k : ℕ} (hw : ∀ b, (D.bag b).card ≤ k+1) :
    ∃ T' : SimpleGraph (B ⊕ A.Fact), ∃ D' : Decomposition A.typedDag.base.underlying T',
      ∀ b, (D'.bag b).card ≤ max k 4+1 := by
  classical
  choose parent hp using hf
  let H := A.typedDag.base.underlying.comap (A.vertexEquiv).symm
  have hedges : ∀ {u v}, H.Adj u v → ∃ b,
      u ∈ A.incidenceBag D b ∧ v ∈ A.incidenceBag D b := by
    have one : ∀ {x y : A.Vertex}, A.Edge x y → ∃ f,
        A.vertexEquiv x ∈ A.piece f ∧ A.vertexEquiv y ∈ A.piece f := by
      intro x y h
      cases h with
      | first f i => exact ⟨f,by simp [vertexEquiv],by simp [vertexEquiv]⟩
      | second f i => exact ⟨f,by simp [vertexEquiv],by simp [vertexEquiv,args]⟩
    intro u v h
    change A.Edge _ _ ∨ A.Edge _ _ at h
    rcases h with h | h
    · obtain ⟨f,h1,h2⟩ := one h
      exact ⟨.inr f,by simpa [incidenceBag] using h1,by simpa [incidenceBag] using h2⟩
    · obtain ⟨f,h1,h2⟩ := one h
      exact ⟨.inr f,by simpa [incidenceBag] using h2,by simpa [incidenceBag] using h1⟩
  let D0 := leafExtension D H parent Sigma.fst (A.incidenceBag D)
    (by intros; simp [incidenceBag])
    (by intro p b; cases b <;> simp [incidenceBag])
    (by
      intro v b hv
      cases b with
      | inl b => simpa [incidenceBag] using hv
      | inr f => exact hp f ((A.base_piece v f).mp hv)) hedges
  have he : ∀ u v, A.typedDag.base.underlying.Adj (A.vertexEquiv.symm u) (A.vertexEquiv.symm v) → H.Adj u v :=
    fun _ _ h => h
  refine ⟨_,D0.mapEquiv A.vertexEquiv.symm he,?_⟩
  intro b
  rw [Decomposition.mapEquiv_card]
  change (A.incidenceBag D b).card ≤ _
  cases b with
  | inl b => simp only [incidenceBag,Finset.card_map]; have := hw b; omega
  | inr f => have := A.piece_card f (ha f.1); change (A.piece f).card ≤ _; omega

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
