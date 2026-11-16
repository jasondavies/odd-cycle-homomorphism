module

public import TreewidthHom.ForestOrientation

@[expose] public section

/-!
# Extending a guess on a feedback vertex set

The combinatorial core of the W[P] membership argument. Fix images for the
vertices of a feedback vertex set `S`. The rest of the graph is a rooted forest.
A pair `(x,a)` is feasible when `a` is compatible with the guessed neighbours of
`x` and every child of `x` has a feasible pair adjacent to `a`. The guess extends
to a homomorphism exactly when it preserves the edges inside `S` and every root
has a feasible pair.
-/
namespace TreewidthHom.Feedback
open SimpleGraph

variable {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (S : Set V) (g : V → W)
  (O : ForestOrientation (G.induce {v | v ∉ S}))

/-- The subtree below `x` maps to `H` with `x ↦ a`, compatibly with the guess `g` on `S`.
The function `b` records the images chosen for the children of `x`. -/
inductive Feasible : ↥{v | v ∉ S} → W → Prop
  | intro (x : ↥{v | v ∉ S}) (a : W) (b : ↥{v | v ∉ S} → W)
      (compat : ∀ s ∈ S, G.Adj x.val s → H.Adj a (g s))
      (adj : ∀ y, O.parent y = some x → H.Adj a (b y))
      (below : ∀ y, O.parent y = some x → Feasible y (b y)) : Feasible x a

/-- The recurrence evaluated from the leaves upwards. -/
theorem feasible_iff (x : ↥{v | v ∉ S}) (a : W) :
    Feasible G H S g O x a ↔
      (∀ s ∈ S, G.Adj x.val s → H.Adj a (g s)) ∧
      ∀ y, O.parent y = some x → ∃ b, H.Adj a b ∧ Feasible G H S g O y b := by
  constructor
  · rintro ⟨_,_,b,hc,ha,hb⟩
    exact ⟨hc,fun y hy => ⟨b y,ha y hy,hb y hy⟩⟩
  · rintro ⟨hc,h⟩
    have ex : ∀ y, ∃ b, O.parent y = some x → H.Adj a b ∧ Feasible G H S g O y b := by
      intro y
      by_cases hy : O.parent y = some x
      · obtain ⟨b,hb⟩ := h y hy
        exact ⟨b,fun _ => hb⟩
      · exact ⟨a,fun h => absurd h hy⟩
    choose b hb using ex
    exact .intro x a b hc (fun y hy => (hb y hy).1) (fun y hy => (hb y hy).2)

/-- A homomorphism makes every pair `(x, φ x)` feasible. -/
theorem feasible_of_hom [Finite V] (φ : G →g H) (hφ : ∀ s ∈ S, φ s = g s)
    (x : ↥{v | v ∉ S}) : Feasible G H S g O x (φ x.val) := by
  obtain ⟨M,hM⟩ := (Set.finite_range O.rank).bddAbove
  have bound : ∀ x, O.rank x ≤ M := fun x => hM ⟨x,rfl⟩
  have all : ∀ k x, M+1 ≤ O.rank x+k → Feasible G H S g O x (φ x.val) := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have := bound x
      omega
    | succ k ih =>
      intro x hx
      refine .intro x _ (fun y => φ y.val) ?_ ?_ ?_
      · intro s hs hadj
        rw [← hφ s hs]
        exact φ.map_rel hadj
      · intro y hy
        exact φ.map_rel (O.parent_spec y x hy).1.symm
      · intro y hy
        have := (O.parent_spec y x hy).2
        exact ih y (by omega)
  exact all (M+1) x (by omega)

/-- Feasible roots give an assignment of the whole forest, built from the roots downwards. -/
theorem exists_assignment [Finite V]
    (hroot : ∀ x, O.parent x = none → ∃ a, Feasible G H S g O x a) :
    ∃ f : ↥{v | v ∉ S} → W, ∀ x, Feasible G H S g O x (f x) ∧
      ∀ p, O.parent x = some p → H.Adj (f p) (f x) := by
  classical
  obtain ⟨M,hM⟩ := (Set.finite_range O.rank).bddAbove
  have bound : ∀ x, O.rank x ≤ M := fun x => hM ⟨x,rfl⟩
  have all : ∀ k, ∃ f : ↥{v | v ∉ S} → W, ∀ x, O.rank x < k →
      Feasible G H S g O x (f x) ∧ ∀ p, O.parent x = some p → H.Adj (f p) (f x) := by
    intro k
    induction k with
    | zero => exact ⟨fun x => g x.val,fun x hx => absurd hx (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨f,hf⟩ := ih
      have ex : ∀ x, O.rank x = k → ∃ a, Feasible G H S g O x a ∧
          ∀ p, O.parent x = some p → H.Adj (f p) a := by
        intro x hx
        rcases hp : O.parent x with _ | p
        · obtain ⟨a,ha⟩ := hroot x hp
          exact ⟨a,ha,fun p h => by simp at h⟩
        · have hr := (O.parent_spec x p hp).2
          obtain ⟨b,hb1,hb2⟩ := ((feasible_iff G H S g O p (f p)).mp
            (hf p (by omega)).1).2 x hp
          refine ⟨b,hb2,fun p' h => ?_⟩
          cases h
          exact hb1
      let f' : ↥{v | v ∉ S} → W := fun x =>
        if h : O.rank x = k then (ex x h).choose else f x
      have keep : ∀ x, O.rank x < k → f' x = f x := by
        intro x hx
        have : ¬ O.rank x = k := by omega
        simp [f',this]
      refine ⟨f',fun x hx => ?_⟩
      by_cases hk : O.rank x = k
      · have hfx : f' x = (ex x hk).choose := by simp [f',hk]
        obtain ⟨h1,h2⟩ := (ex x hk).choose_spec
        rw [hfx]
        refine ⟨h1,fun p hp => ?_⟩
        have hr := (O.parent_spec x p hp).2
        rw [keep p (by omega)]
        exact h2 p hp
      · have hlt : O.rank x < k := by omega
        obtain ⟨h1,h2⟩ := hf x hlt
        rw [keep x hlt]
        refine ⟨h1,fun p hp => ?_⟩
        have hr := (O.parent_spec x p hp).2
        rw [keep p (by omega)]
        exact h2 p hp
  obtain ⟨f,hf⟩ := all (M+1)
  exact ⟨f,fun x => hf x (by have := bound x; omega)⟩

/-- The guess extends to a homomorphism exactly when it preserves the edges inside
the feedback vertex set and every root of the remaining forest has a feasible pair. -/
theorem extends_iff [Finite V] :
    (∃ φ : G →g H, ∀ s ∈ S, φ s = g s) ↔
      (∀ s ∈ S, ∀ s' ∈ S, G.Adj s s' → H.Adj (g s) (g s')) ∧
      ∀ x, O.parent x = none → ∃ a, Feasible G H S g O x a := by
  classical
  constructor
  · rintro ⟨φ,hφ⟩
    refine ⟨fun s hs s' hs' hadj => ?_,fun x _ => ⟨_,feasible_of_hom G H S g O φ hφ x⟩⟩
    rw [← hφ s hs,← hφ s' hs']
    exact φ.map_rel hadj
  · rintro ⟨hS,hroot⟩
    obtain ⟨f,hf⟩ := exists_assignment G H S g O hroot
    let φ : V → W := fun v => if h : v ∈ S then g v else f ⟨v,h⟩
    have hin : ∀ v, v ∈ S → φ v = g v := fun v h => by simp [φ,h]
    have hout : ∀ v (h : v ∉ S), φ v = f ⟨v,h⟩ := fun v h => by simp [φ,h]
    have mixed : ∀ u v, u ∈ S → v ∉ S → G.Adj u v → H.Adj (φ u) (φ v) := by
      intro u v hu hv hadj
      rw [hin u hu,hout v hv]
      exact (((feasible_iff G H S g O ⟨v,hv⟩ _).mp (hf ⟨v,hv⟩).1).1 u hu hadj.symm).symm
    refine ⟨⟨φ,?_⟩,hin⟩
    intro u v hadj
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · rw [hin u hu,hin v hv]
      exact hS u hu v hv hadj
    · exact mixed u v hu hv hadj
    · exact (mixed v u hv hu hadj.symm).symm
    · rw [hout u hu,hout v hv]
      rcases O.edge ⟨u,hu⟩ ⟨v,hv⟩ hadj with h | h
      · exact ((hf ⟨u,hu⟩).2 _ h).symm
      · exact (hf ⟨v,hv⟩).2 _ h

/-- For a feedback vertex set, a suitable rooting exists and works for every guess. -/
theorem exists_orientation_extends [Finite V] (hS : (G.induce {v | v ∉ S}).IsAcyclic) :
    ∃ O : ForestOrientation (G.induce {v | v ∉ S}), ∀ g : V → W,
      (∃ φ : G →g H, ∀ s ∈ S, φ s = g s) ↔
        (∀ s ∈ S, ∀ s' ∈ S, G.Adj s s' → H.Adj (g s) (g s')) ∧
        ∀ x, O.parent x = none → ∃ a, Feasible G H S g O x a := by
  obtain ⟨O⟩ := exists_forestOrientation _ hS
  exact ⟨O,fun g => extends_iff G H S g O⟩

end TreewidthHom.Feedback
