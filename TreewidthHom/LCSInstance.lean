module

public import TreewidthHom.UnaryBinary
public import TreewidthHom.LCS

@[expose] public section

/-! # The actual fixed-schema LCS source and target structures -/
namespace TreewidthHom.LCSInstance

/-- A row consists of ℓ padded blocks, followed by its final endpoint. -/
abbrev Position (N ℓ : ℕ) := (Fin ℓ × Fin (N+1)) ⊕ Unit

def boundary {N ℓ : ℕ} (j : Fin (ℓ+1)) : Position N ℓ :=
  if h : j.val < ℓ then .inl (⟨j.val,h⟩,0) else .inr ()

@[simp] theorem boundary_castSucc {N ℓ : ℕ} (j : Fin ℓ) :
    boundary (N := N) j.castSucc = .inl (j,0) := by simp [boundary,j.isLt]

@[simp] theorem boundary_last (N ℓ : ℕ) : boundary (N := N) (Fin.last ℓ) = .inr () := by
  simp [boundary]

inductive QueryVertex (k N ℓ : ℕ)
  | anchor : Fin (k+1) → QueryVertex k N ℓ
  | row : Fin k → Position N ℓ → QueryVertex k N ℓ
  | letter : Fin ℓ → QueryVertex k N ℓ
  deriving DecidableEq

inductive TargetVertex {k : ℕ} (words : Fin k → List Bool)
  | anchor : Fin (k+1) → TargetVertex words
  | pos : (i : Fin k) → Fin ((words i).length+1) → TargetVertex words
  | bit : Bool → TargetVertex words
  deriving DecidableEq

/-- Next, Begin, Step, Advance, Letter, in that order. -/
inductive QueryEdge (k N ℓ : ℕ) : Fin 5 → QueryVertex k N ℓ → QueryVertex k N ℓ → Prop
  | next (i : Fin k) : QueryEdge k N ℓ 0 (.anchor i.castSucc) (.anchor i.succ)
  | begin (i : Fin k) : QueryEdge k N ℓ 1 (.anchor i.succ) (.row i (boundary 0))
  | step (i : Fin k) (j : Fin ℓ) (s : Fin N) :
      QueryEdge k N ℓ 2 (.row i (.inl (j,s.castSucc))) (.row i (.inl (j,s.succ)))
  | advance (i : Fin k) (j : Fin ℓ) :
      QueryEdge k N ℓ 3 (.row i (.inl (j,Fin.last N))) (.row i (boundary j.succ))
  | letter (i : Fin k) (j : Fin ℓ) :
      QueryEdge k N ℓ 4 (.row i (boundary j.succ)) (.letter j)

def query (k N ℓ : ℕ) : UnaryBinary (QueryVertex k N ℓ) where
  root v := v = .anchor 0
  binary := QueryEdge k N ℓ

def occurrence {k : ℕ} {words : Fin k → List Bool} (i : Fin k) (j : Fin (words i).length) :
    Fin ((words i).length+1) := ⟨j.val+1,by have := j.isLt; omega⟩

inductive TargetEdge {k : ℕ} (words : Fin k → List Bool) :
    Fin 5 → TargetVertex words → TargetVertex words → Prop
  | next (i : Fin k) : TargetEdge words 0 (.anchor i.castSucc) (.anchor i.succ)
  | begin (i : Fin k) : TargetEdge words 1 (.anchor i.succ) (.pos i 0)
  | step (i : Fin k) (a b : Fin ((words i).length+1)) (h : Step a.val b.val) :
      TargetEdge words 2 (.pos i a) (.pos i b)
  | advance (i : Fin k) (a b : Fin ((words i).length+1)) (h : b.val = a.val+1) :
      TargetEdge words 3 (.pos i a) (.pos i b)
  | letter (i : Fin k) (j : Fin (words i).length) :
      TargetEdge words 4 (.pos i (occurrence i j)) (.bit ((words i).get j))

def target {k : ℕ} (words : Fin k → List Bool) : UnaryBinary (TargetVertex words) where
  root v := v = .anchor 0
  binary := TargetEdge words

namespace TargetEdge
variable {k : ℕ} {words : Fin k → List Bool}

theorem next_cases {u v : TargetVertex words} (h : TargetEdge words 0 u v) :
    ∃ i : Fin k, u = .anchor i.castSucc ∧ v = .anchor i.succ := by
  cases h with
  | next i => exact ⟨i,rfl,rfl⟩

theorem next_out {i : Fin k} {v : TargetVertex words}
    (h : TargetEdge words 0 (.anchor i.castSucc) v) : v = .anchor i.succ := by
  obtain ⟨j,hj,hv⟩ := next_cases h
  have he : i = j := Fin.castSucc_injective k (TargetVertex.anchor.inj hj)
  subst j
  exact hv

theorem begin_cases {u v : TargetVertex words} (h : TargetEdge words 1 u v) :
    ∃ i : Fin k, u = .anchor i.succ ∧ v = .pos i 0 := by
  cases h with
  | begin i => exact ⟨i,rfl,rfl⟩

theorem begin_out {i : Fin k} {v : TargetVertex words}
    (h : TargetEdge words 1 (.anchor i.succ) v) : v = .pos i 0 := by
  obtain ⟨j,hj,hv⟩ := begin_cases h
  have he : i = j := Fin.succ_injective k (TargetVertex.anchor.inj hj)
  subst j
  exact hv

theorem step_out {i : Fin k} {a : Fin ((words i).length+1)} {v : TargetVertex words}
    (h : TargetEdge words 2 (.pos i a) v) :
    ∃ b, v = .pos i b ∧ Step a.val b.val := by
  cases h with
  | step i a b he => exact ⟨b,rfl,he⟩

theorem advance_out {i : Fin k} {a : Fin ((words i).length+1)} {v : TargetVertex words}
    (h : TargetEdge words 3 (.pos i a) v) :
    ∃ b, v = .pos i b ∧ b.val = a.val+1 := by
  cases h with
  | advance i a b he => exact ⟨b,rfl,he⟩

theorem letter_out {i : Fin k} {a : Fin ((words i).length+1)} {v : TargetVertex words}
    (h : TargetEdge words 4 (.pos i a) v) :
    ∃ j, a = occurrence i j ∧ v = .bit ((words i).get j) := by
  cases h with
  | letter i j => exact ⟨j,rfl,rfl⟩

theorem step_values {i : Fin k} {a b : Fin ((words i).length+1)}
    (h : TargetEdge words 2 (.pos i a) (.pos i b)) : Step a.val b.val := by
  cases h with
  | step i a b he => exact he

theorem advance_values {i : Fin k} {a b : Fin ((words i).length+1)}
    (h : TargetEdge words 3 (.pos i a) (.pos i b)) : b.val = a.val+1 := by
  cases h with
  | advance i a b he => exact he

end TargetEdge
end TreewidthHom.LCSInstance
