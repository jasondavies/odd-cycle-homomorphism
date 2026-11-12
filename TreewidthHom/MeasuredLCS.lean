module
public import TreewidthHom.MeasuredSchema
@[expose] public section
set_option synthInstance.maxSize 1000
set_option backward.isDefEq.respectTransparency false
namespace TreewidthHom.Executable
open LCSInstance EnumRun
namespace Decision

def both {p q : Prop} (a : Measured (Decidable p)) (b : Measured (Decidable q)) := and p q a b
def either {p q : Prop} (a : Measured (Decidable p)) (b : Measured (Decidable q)) := or p q a b
def ex {n : ℕ} {p : Fin n → Prop} (test : ∀ i, Measured (Decidable (p i))) := existsFin p test

abbrev Level {p : Prop} (a : Measured (Decidable p)) (d s : ℕ) := a.cost ≤ budget d s

theorem Level.lift {p : Prop} {a : Measured (Decidable p)} {d d' s : ℕ}
    (h : Level a d s) (hd : d ≤ d') : Level a d' s := h.trans (budget_mono hd s)

theorem level_atom (p : Prop) [Decidable p] {q s : ℕ} (h : q ≤ s+1) : Level (atom p q) 0 s := h

theorem level_both {p q : Prop} {a : Measured (Decidable p)} {b : Measured (Decidable q)}
    {d s : ℕ} (ha : Level a d s) (hb : Level b d s) : Level (both a b) (d+1) s := by
  change a.cost+b.cost+1 ≤ grow (budget d s)
  unfold grow
  nlinarith [sq_nonneg (budget d s : ℤ)]

theorem level_either {p q : Prop} {a : Measured (Decidable p)} {b : Measured (Decidable q)}
    {d s : ℕ} (ha : Level a d s) (hb : Level b d s) : Level (either a b) (d+1) s :=
  level_both ha hb

theorem level_ex {n : ℕ} {p : Fin n → Prop} {test : ∀ i, Measured (Decidable (p i))}
    {d s : ℕ} (hn : n ≤ s+1) (ht : ∀ i, Level (test i) d s) : Level (ex test) (d+1) s := by
  have h := existsFin_cost p test ht
  have hn' : n ≤ budget d s := hn.trans (budget_mono (Nat.zero_le d) s)
  have hs := Nat.pow_le_pow_left (Nat.add_le_add_right hn' 1) 2
  have hm := Nat.mul_le_mul_left (budget d s+1) hn'
  change (existsFin p test).cost ≤ grow (budget d s)
  unfold grow
  nlinarith [sq_nonneg (budget d s : ℤ)]

end Decision

open Decision in
def queryTest {k N ℓ : ℕ} (q : ℕ) (r : Fin 5) (u v : QueryVertex k N ℓ) :
    Measured (Decidable (QueryEdge k N ℓ r u v)) :=
  ofIff (queryEdge_iff r u v).symm
    (either (both (atom (r=0) q) (ex (fun i : Fin k =>
      both (atom (u = .anchor i.castSucc) q) (atom (v = .anchor i.succ) q))))
    (either (both (atom (r=1) q) (ex (fun i : Fin k =>
      both (atom (u = .anchor i.succ) q) (atom (v = .row i (boundary 0)) q))))
    (either (both (atom (r=2) q) (ex (fun i : Fin k => ex (fun j : Fin ℓ => ex (fun t : Fin N =>
      both (atom (u = .row i (.inl (j,t.castSucc))) q) (atom (v = .row i (.inl (j,t.succ))) q))))))
    (either (both (atom (r=3) q) (ex (fun i : Fin k => ex (fun j : Fin ℓ =>
      both (atom (u = .row i (.inl (j,Fin.last N))) q) (atom (v = .row i (boundary j.succ)) q)))))
    (both (atom (r=4) q) (ex (fun i : Fin k => ex (fun j : Fin ℓ =>
      both (atom (u = .row i (boundary j.succ)) q) (atom (v = .letter j) q)))))))))

open Decision in
def targetTest {k : ℕ} (words : Fin k → List Bool) (q : ℕ) (r : Fin 5) (u v : TargetVertex words) :
    Measured (Decidable (TargetEdge words r u v)) :=
  ofIff (targetEdge_iff words r u v).symm
    (either (both (atom (r=0) q) (ex (fun i : Fin k =>
      both (atom (u = .anchor i.castSucc) q) (atom (v = .anchor i.succ) q))))
    (either (both (atom (r=1) q) (ex (fun i : Fin k =>
      both (atom (u = .anchor i.succ) q) (atom (v = .pos i 0) q))))
    (either (both (atom (r=2) q) (ex (fun i : Fin k => ex (fun a : Fin ((words i).length+1) => ex (fun b : Fin ((words i).length+1) =>
      both (either (atom (b.val = a.val) q) (atom (b.val = a.val+1) q))
        (both (atom (u = .pos i a) q) (atom (v = .pos i b) q)))))))
    (either (both (atom (r=3) q) (ex (fun i : Fin k => ex (fun a : Fin ((words i).length+1) => ex (fun b : Fin ((words i).length+1) =>
      both (atom (b.val = a.val+1) q) (both (atom (u = .pos i a) q) (atom (v = .pos i b) q)))))))
    (both (atom (r=4) q) (ex (fun i : Fin k => ex (fun j : Fin ((words i).length) =>
      both (atom (u = .pos i (occurrence i j)) q) (atom (v = .bit ((words i).get j)) q)))))))))

/-- Every leaf is a supplied comparison/word-access primitive of cost q;
all finite existential searches themselves are expanded and charged. -/
theorem queryTest_level {k N ℓ q s : ℕ} (hk : k ≤ s) (hN : N ≤ s) (hℓ : ℓ ≤ s) (hq : q ≤ s+1)
    (r : Fin 5) (u v : QueryVertex k N ℓ) : (queryTest q r u v).cost ≤ budget 12 s := by
  unfold queryTest
  change Decision.Level _ 12 s
  -- Every branch is promoted to a common depth before disjunction composition.
  have atomB : ∀ p : Prop, ∀ [Decidable p], Decision.Level (Decision.atom p q) 0 s := fun _ _ => hq
  apply Decision.Level.lift (d := 9) (hd := by omega)
  apply Decision.level_either
  · apply Decision.Level.lift (d := 3) (hd := by omega)
    apply Decision.level_both
    · exact Decision.Level.lift (atomB _) (by omega)
    · apply Decision.level_ex (by omega)
      intro i
      exact Decision.level_both (atomB _) (atomB _)
  · apply Decision.level_either
    · apply Decision.Level.lift (d := 3) (hd := by omega)
      apply Decision.level_both
      · exact Decision.Level.lift (atomB _) (by omega)
      · apply Decision.level_ex (by omega)
        intro i
        exact Decision.level_both (atomB _) (atomB _)
    · apply Decision.level_either
      · apply Decision.Level.lift (d := 5) (hd := by omega)
        apply Decision.level_both
        · exact Decision.Level.lift (atomB _) (by omega)
        · apply Decision.level_ex (by omega); intro i
          apply Decision.level_ex (by omega); intro j
          apply Decision.level_ex (by omega); intro t
          exact Decision.level_both (atomB _) (atomB _)
      · apply Decision.level_either
        all_goals
          apply Decision.Level.lift (d := 4) (hd := by omega)
          apply Decision.level_both
          · exact Decision.Level.lift (atomB _) (by omega)
          · apply Decision.level_ex (by omega); intro i
            apply Decision.level_ex (by omega); intro j
            exact Decision.level_both (atomB _) (atomB _)

theorem targetTest_level {k q s : ℕ} (words : Fin k → List Bool)
    (hk : k ≤ s) (hN : ∀ i, (words i).length ≤ s) (hq : q ≤ s+1)
    (r : Fin 5) (u v : TargetVertex words) : (targetTest words q r u v).cost ≤ budget 12 s := by
  unfold targetTest
  change Decision.Level _ 12 s
  have atomB : ∀ p : Prop, ∀ [Decidable p], Decision.Level (Decision.atom p q) 0 s := fun _ _ => hq
  apply Decision.Level.lift (d := 10) (hd := by omega)
  apply Decision.level_either
  · apply Decision.Level.lift (d := 3) (hd := by omega)
    apply Decision.level_both
    · exact Decision.Level.lift (atomB _) (by omega)
    · apply Decision.level_ex (by omega); intro i
      exact Decision.level_both (atomB _) (atomB _)
  · apply Decision.level_either
    · apply Decision.Level.lift (d := 3) (hd := by omega)
      apply Decision.level_both
      · exact Decision.Level.lift (atomB _) (by omega)
      · apply Decision.level_ex (by omega); intro i
        exact Decision.level_both (atomB _) (atomB _)
    · apply Decision.level_either
      · apply Decision.Level.lift (d := 6) (hd := by omega)
        apply Decision.level_both
        · exact Decision.Level.lift (atomB _) (by omega)
        · apply Decision.level_ex (by omega); intro i
          apply Decision.level_ex (by have := hN i; omega); intro a
          apply Decision.level_ex (by have := hN i; omega); intro b
          exact Decision.level_both (Decision.level_either (atomB _) (atomB _))
            (Decision.level_both (atomB _) (atomB _))
      · apply Decision.level_either
        · apply Decision.level_both
          · exact Decision.Level.lift (atomB _) (by omega)
          · apply Decision.level_ex (by omega); intro i
            apply Decision.level_ex (by have := hN i; omega); intro a
            apply Decision.level_ex (by have := hN i; omega); intro b
            exact Decision.level_both (Decision.Level.lift (atomB _) (show 0 ≤ 1 by omega))
              (Decision.level_both (atomB _) (atomB _))
        · apply Decision.Level.lift (d := 4) (hd := by omega)
          apply Decision.level_both
          · exact Decision.Level.lift (atomB _) (by omega)
          · apply Decision.level_ex (by omega); intro i
            apply Decision.level_ex (by have := hN i; omega); intro j
            exact Decision.level_both (atomB _) (atomB _)

/-- The branch test for unary/binary schema dispatch is charged too. -/
def holdsTest {V : Type} (A : UnaryBinary V)
    (rootTest : ∀ v, Measured (Decidable (A.root v)))
    (binaryTest : ∀ r u v, Measured (Decidable (A.binary r u v)))
    (r : Fin 6) (t : Fin (Relational.schemaArity r) → V) :
    Measured (Decidable (A.asRelational.holds r t)) :=
  if hr : r = 0 then
    let a := rootTest (t ⟨0,by simp [Relational.schemaArity,hr]⟩)
    ⟨by simpa [UnaryBinary.asRelational,hr] using a.value,a.cost+1⟩
  else
    let a := binaryTest ⟨r.val-1,by have := r.isLt; omega⟩
      (t ⟨0,by simp [Relational.schemaArity,hr]⟩) (t ⟨1,by simp [Relational.schemaArity,hr]⟩)
    ⟨by simpa [UnaryBinary.asRelational,hr] using a.value,a.cost+1⟩

theorem holdsTest_level {V : Type} (A : UnaryBinary V)
    (rootTest : ∀ v, Measured (Decidable (A.root v)))
    (binaryTest : ∀ r u v, Measured (Decidable (A.binary r u v))) {d s : ℕ}
    (hroot : ∀ v, (rootTest v).cost ≤ budget d s)
    (hbin : ∀ r u v, (binaryTest r u v).cost ≤ budget d s)
    (r : Fin 6) (t : Fin (Relational.schemaArity r) → V) :
    (holdsTest A rootTest binaryTest r t).cost ≤ budget (d+1) s := by
  unfold holdsTest
  split_ifs with hr
  · have hh := hroot (t ⟨0,by simp [Relational.schemaArity,hr]⟩)
    change (rootTest _).cost+1 ≤ grow (budget d s)
    unfold grow
    nlinarith [sq_nonneg (budget d s : ℤ)]
  · have hh := hbin ⟨r.val-1,by have := r.isLt; omega⟩
      (t ⟨0,by simp [Relational.schemaArity,hr]⟩) (t ⟨1,by simp [Relational.schemaArity,hr]⟩)
    change (binaryTest _ _ _).cost+1 ≤ grow (budget d s)
    unfold grow
    nlinarith [sq_nonneg (budget d s : ℤ)]

def queryHoldsTest (k N ℓ q : ℕ) :=
  holdsTest (query k N ℓ) (fun v => Decision.atom (v = .anchor 0) q) (queryTest q)

def targetHoldsTest {k : ℕ} (words : Fin k → List Bool) (q : ℕ) :=
  holdsTest (target words) (fun v => Decision.atom (v = .anchor 0) q) (targetTest words q)

theorem queryHoldsTest_level {k N ℓ q s : ℕ} (hk : k ≤ s) (hN : N ≤ s) (hℓ : ℓ ≤ s) (hq : q ≤ s+1)
    (r : Fin 6) (t : Fin (Relational.schemaArity r) → QueryVertex k N ℓ) :
    (queryHoldsTest k N ℓ q r t).cost ≤ budget 13 s :=
  holdsTest_level _ _ _ (fun _ => hq.trans (budget_mono (by omega : 0 ≤ 12) s))
    (queryTest_level hk hN hℓ hq) r t

theorem targetHoldsTest_level {k q s : ℕ} (words : Fin k → List Bool)
    (hk : k ≤ s) (hN : ∀ i, (words i).length ≤ s) (hq : q ≤ s+1)
    (r : Fin 6) (t : Fin (Relational.schemaArity r) → TargetVertex words) :
    (targetHoldsTest words q r t).cost ≤ budget 13 s :=
  holdsTest_level _ _ _ (fun _ => hq.trans (budget_mono (by omega : 0 ≤ 12) s))
    (targetTest_level words hk hN hq) r t

end TreewidthHom.Executable
