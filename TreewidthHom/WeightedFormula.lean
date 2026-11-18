module

public import TreewidthHom.GraftTree

@[expose] public section

namespace TreewidthHom.WeightedFormula
open SimpleGraph

inductive Gate (X : Type)
  | literal (variableName : X)
  | conj
  | disj
  deriving DecidableEq

/-- A formula in node-table form. The left summand is the root, the right summand
indexes the nonroot occurrences. Repeated literals may name the same variable. -/
abbrev Node (P : Type) := Unit ⊕ P

structure Formula (P X : Type) extends Graft Unit P where
  kind : Node P → Gate X
  parent_not_literal : ∀ p x, kind (parent p) ≠ .literal x

namespace Formula
variable {P X : Type} (F : Formula P X)

abbrev tree := F.toGraft.graph ⊥

private theorem rank_lt (p : P) : F.toGraft.rank (F.parent p) < F.toGraft.rank (.inr p) := by
  cases h : F.parent p with
  | inl u => simp [Graft.rank]
  | inr q => exact Nat.succ_lt_succ (F.decreases p q h)

noncomputable def fuel [Fintype P] (v : Node P) : ℕ :=
  Finset.univ.sup F.toGraft.rank - F.toGraft.rank v

theorem child_lt [Fintype P] (p : P) {v : Node P} (h : F.parent p = v) :
    F.fuel (.inr p) < F.fuel v := by
  subst v
  have := F.rank_lt p
  have := Finset.le_sup (s := Finset.univ) (f := F.toGraft.rank) (Finset.mem_univ (.inr p))
  unfold fuel
  omega

/-- Ordinary truth under the assignment whose true variables are U. -/
def eval [Fintype P] (U : Set X) (v : Node P) : Prop :=
  match F.kind v with
  | .literal x => x ∉ U
  | .conj => ∀ p, (h : F.parent p = v) → eval U (.inr p)
  | .disj => ∃ p, ∃ _h : F.parent p = v, eval U (.inr p)
termination_by F.fuel v
decreasing_by all_goals apply F.child_lt; assumption

/-- A gate colour records its owner and, for disjunction, its chosen child. -/
abbrev Colour (P X : Type) := X ⊕ (Node P × Option P)

def active (v : Node P) (c : Colour P X) : Prop :=
  match F.kind v with
  | .literal x => c = .inl x
  | .conj => c = .inr (v, none)
  | .disj => ∃ p, F.parent p = v ∧ c = .inr (v, some p)

def inactive (p : P) : Colour P X := .inr (F.parent p,
  match F.kind (F.parent p) with | .disj => some p | _ => none)

def allowed (v : Node P) (c : Colour P X) : Prop :=
  F.active v c ∨ ∃ p, v = .inr p ∧ c = F.inactive p

abbrev Vertex (k : ℕ) (P : Type) := Fin k ⊕ Node P

def graph (k : ℕ) : SimpleGraph (Vertex k P) where
  Adj
    | .inl i, .inl j => i ≠ j
    | .inr u, .inr v => F.tree.Adj u v
    | .inl _, .inr v | .inr v, .inl _ => ∃ x, F.kind v = .literal x
  symm := ⟨by rintro (i|u) (j|v) h; exacts [Ne.symm h, h, h, F.tree.adj_symm h]⟩
  loopless := ⟨by rintro (i|v); exacts [fun h => h rfl, F.tree.loopless.irrefl v]⟩

def domain {k : ℕ} : Vertex k P → Colour P X → Prop
  | .inl _, c => ∃ x, c = .inl x
  | .inr v, c => F.allowed v c

def Proper {k : ℕ} (c : Vertex k P → Colour P X) : Prop :=
  (∀ v, F.domain v (c v)) ∧ ∀ u v, (F.graph k).Adj u v → c u ≠ c v

private theorem active_cases {v : Node P} {c : Colour P X} (h : F.active v c) :
    (∃ x, F.kind v = .literal x ∧ c = .inl x) ∨ ∃ i, c = .inr (v,i) := by
  cases hv : F.kind v with
  | literal x => exact Or.inl ⟨x, rfl, by simpa [active, hv] using h⟩
  | conj => exact Or.inr ⟨none, by simpa [active, hv] using h⟩
  | disj =>
    obtain ⟨p, _, hc⟩ := (show ∃ p, _ ∧ _ from by simpa [active, hv] using h)
    exact Or.inr ⟨some p, hc⟩

/-- A parent colour can collide with a child's list only at its inactive colour. -/
private theorem ne_active_child (p : P) {a b : Colour P X}
    (ha : F.allowed (F.parent p) a) (hb : F.active (.inr p) b) : a ≠ b := by
  have owner : ∃ v i, a = .inr (v,i) ∧ F.toGraft.rank v ≤ F.toGraft.rank (F.parent p) := by
    rcases ha with ha | ⟨q,hq,rfl⟩
    · rcases F.active_cases ha with ⟨x,hx,_⟩ | ⟨i,hi⟩
      · exact (F.parent_not_literal p x hx).elim
      · exact ⟨_, i, hi, le_rfl⟩
    · exact ⟨_, _, rfl, hq ▸ (F.rank_lt q).le⟩
  obtain ⟨v,i,rfl,hv⟩ := owner
  rcases F.active_cases hb with ⟨x,_,rfl⟩ | ⟨j,rfl⟩
  · simp
  · intro h
    have he := congrArg Prod.fst (Sum.inr.inj h)
    change v = .inr p at he
    have := F.rank_lt p
    rw [he] at hv
    omega

private theorem inactive_ne_inactive {p q : P} (h : F.parent p = .inr q) :
    F.inactive q ≠ F.inactive p := by
  intro he
  have eq := congrArg Prod.fst (Sum.inr.inj he)
  change F.parent q = F.parent p at eq
  have := F.rank_lt q
  rw [eq, h] at this
  exact (lt_irrefl _ this)

private theorem of_colouring [Fintype P] {k : ℕ} {s : Fin k → X}
    {c : Vertex k P → Colour P X} (hc : F.Proper c) (hs : ∀ i, c (.inl i) = .inl (s i)) :
    ∀ v, F.active v (c (.inr v)) → F.eval (Set.range s) v := by
  intro v
  induction h : F.fuel v using Nat.strong_induction_on generalizing v with
  | h n ih =>
    intro ha
    have child (p : P) (hp : F.parent p = v) (forced : c (.inr v) = F.inactive p) :
        F.eval (Set.range s) (.inr p) := by
      apply ih _ (h ▸ F.child_lt p hp) _ rfl
      rcases hc.1 (.inr (.inr p)) with good | ⟨q, eq, off⟩
      · exact good
      · cases Sum.inr.inj eq
        have adj := F.toGraft.parent_adj (⊥ : SimpleGraph Unit) p
        rw [hp] at adj
        exact (hc.2 _ _ (show (F.graph k).Adj (.inr (.inr p)) (.inr v) from adj)
          (off.trans forced.symm)).elim
    rw [eval]
    cases hv : F.kind v with
    | literal x =>
      have col : c (.inr v) = .inl x := by simpa [active,hv] using ha
      rintro ⟨i,rfl⟩
      exact hc.2 _ _ (show (F.graph k).Adj (.inl i) (.inr v) from ⟨_,hv⟩)
        ((hs i).trans col.symm)
    | conj =>
      intro p hp
      apply child p hp
      simpa [active, inactive, hp, hv] using ha
    | disj =>
      obtain ⟨p,hp,col⟩ := (show ∃ p, F.parent p = v ∧ _ from by simpa [active,hv] using ha)
      exact ⟨p,hp,child p hp (by simpa [inactive,hp,hv] using col)⟩

/-- At a true node choose a witness colour. A child forced by this colour is true. -/
private theorem witness [Fintype P] {U : Set X} {v : Node P} (hv : F.eval U v) :
    ∃ c, F.active v c ∧ (∀ x, c = .inl x → x ∉ U) ∧
      ∀ p, F.parent p = v → c = F.inactive p → F.eval U (.inr p) := by
  rw [eval] at hv
  cases hg : F.kind v with
  | literal x =>
    refine ⟨.inl x, by simp [active,hg], ?_, ?_⟩
    · rintro y he
      cases Sum.inl.inj he
      simpa [hg] using hv
    · simp [inactive]
  | conj =>
    have allTrue : ∀ p, F.parent p = v → F.eval U (.inr p) := by simpa [hg] using hv
    exact ⟨.inr (v,none), by simp [active,hg], by simp, fun p hp _ => allTrue p hp⟩
  | disj =>
    obtain ⟨q,hq,ht⟩ := (show ∃ q, F.parent q = v ∧ F.eval U (.inr q) from by simpa [hg] using hv)
    refine ⟨.inr (v,some q), ?_, by simp, ?_⟩
    · simp only [active,hg]
      exact ⟨q,hq,rfl⟩
    · intro p hp he
      have eq : q = p := by simpa [inactive,hp,hg] using he
      exact eq ▸ ht

/-- For any injection assigning the selectors, extension is equivalent to truth
at the root under exactly its image. -/
theorem extends_iff [Fintype P] {k : ℕ} (s : Fin k ↪ X) :
    (∃ c, F.Proper c ∧ ∀ i, c (.inl i) = .inl (s i)) ↔ F.eval (Set.range s) (.inl ()) := by
  classical
  constructor
  · rintro ⟨c,hc,hs⟩
    apply F.of_colouring hc hs
    rcases hc.1 (.inr (.inl ())) with a | ⟨p,h,_⟩
    · exact a
    · contradiction
  · intro root
    let col (v : Node P) : Colour P X := if h : F.eval (Set.range s) v then
      (F.witness h).choose else match v with
      | .inl _ => (F.witness root).choose
      | .inr p => F.inactive p
    have spec (v : Node P) (h : F.eval (Set.range s) v) := (F.witness h).choose_spec
    have allowed' (v : Node P) : F.allowed v (col v) := by
      by_cases h : F.eval (Set.range s) v
      · exact Or.inl (by simpa [col,h] using (spec v h).1)
      · cases v with
        | inl u => exact (h root).elim
        | inr p => exact Or.inr ⟨p,rfl,by simp [col,h]⟩
    have edge (p : P) : col (F.parent p) ≠ col (.inr p) := by
      by_cases h : F.eval (Set.range s) (.inr p)
      · apply F.ne_active_child p (allowed' _)
        simpa [col,h] using (spec _ h).1
      · have off : col (.inr p) = F.inactive p := by simp [col,h]
        rw [off]
        by_cases hp : F.eval (Set.range s) (F.parent p)
        · intro eq
          exact h ((spec _ hp).2.2 p rfl (by simpa [col,hp] using eq))
        · cases hq : F.parent p with
          | inl u => exact (hp (hq ▸ root)).elim
          | inr q =>
            rw [hq] at hp
            simpa [col,hp] using F.inactive_ne_inactive hq
    have cross (i : Fin k) (v : Node P) : col v ≠ .inl (s i) := by
      by_cases h : F.eval (Set.range s) v
      · intro eq
        exact (spec _ h).2.1 _ (by simpa [col,h] using eq) ⟨i,rfl⟩
      · cases v with
        | inl u => exact (h root).elim
        | inr p => simp [col,h,inactive]
    refine ⟨Sum.elim (fun i => .inl (s i)) col, ⟨?_,?_⟩, fun _ => rfl⟩
    · rintro (i|v)
      · exact ⟨s i,rfl⟩
      · exact allowed' v
    · rintro (i|u) (j|v) adj
      · exact fun eq => adj (s.injective (Sum.inl.inj eq))
      · exact (cross i v).symm
      · exact cross j u
      · cases u with
        | inl r =>
          cases v with
          | inl t => exact adj.elim
          | inr p => exact (show F.parent p = _ from adj) ▸ edge p
        | inr p =>
          cases v with
          | inl r => exact (show F.parent p = _ from adj) ▸ (edge p).symm
          | inr q =>
            rcases adj with h | h
            · exact h ▸ (edge p).symm
            · exact h ▸ edge q

end Formula
end TreewidthHom.WeightedFormula
