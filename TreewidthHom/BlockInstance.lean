module

public import TreewidthHom.LCSInstance

@[expose] public section

/-!
# LCS over arbitrary alphabets: letters as blocks of bits

Every letter is a block of `L+1` bits on its target row. A query chain makes `N`
Step moves, one Advance move, which must enter a block, and `L` Begin moves inside
that block. The `L+1` vertices reached by the last `L+1` moves read the block's
bits through Letter facts shared by all strings. For `L = 0` this is the binary
construction of `LCSInstance`. The fixed schema is unchanged.
-/
namespace TreewidthHom.BlockLCS
open LCSInstance (Position boundary TargetVertex occurrence)

/-- The successor of a chain vertex: the next chain vertex, or the next boundary. -/
def nxt {M ℓ : ℕ} (j : Fin ℓ) (s : Fin (M+1)) : Position M ℓ :=
  if h : s.val < M then .inl (j,⟨s.val+1,by omega⟩) else boundary j.succ

@[simp] theorem nxt_castSucc {M ℓ : ℕ} (j : Fin ℓ) (s : Fin M) :
    nxt j s.castSucc = .inl (j,s.succ) := by
  unfold nxt
  rw [dite_eq_left (by simp : s.castSucc.val < M)]
  rfl

@[simp] theorem nxt_last {M ℓ : ℕ} (j : Fin ℓ) : nxt j (Fin.last M) = boundary j.succ := by
  simp [nxt]

/-- The relation on the chain edge leaving index `s`: Step, then Advance, then Begin. -/
def chainRel (N s : ℕ) : Fin 5 := if s < N then 2 else if s = N then 3 else 1

theorem chainRel_step {N s : ℕ} (h : s < N) : chainRel N s = 2 := by simp [chainRel,h]
theorem chainRel_advance (N : ℕ) : chainRel N N = 3 := by simp [chainRel]
theorem chainRel_read {N s : ℕ} (h : N < s) : chainRel N s = 1 := by
  have h1 : ¬ s < N := by omega
  have h2 : s ≠ N := by omega
  simp [chainRel,h1,h2]

inductive QueryVertex (k N ℓ L : ℕ)
  | anchor : Fin (k+1) → QueryVertex k N ℓ L
  | row : Fin k → Position (N+L) ℓ → QueryVertex k N ℓ L
  | letter : Fin ℓ → Fin (L+1) → QueryVertex k N ℓ L
  deriving DecidableEq

/-- Next, Begin, Step, Advance, Letter, in that order. -/
inductive QueryEdge (k N ℓ L : ℕ) :
    Fin 5 → QueryVertex k N ℓ L → QueryVertex k N ℓ L → Prop
  | next (i : Fin k) : QueryEdge k N ℓ L 0 (.anchor i.castSucc) (.anchor i.succ)
  | begin (i : Fin k) : QueryEdge k N ℓ L 1 (.anchor i.succ) (.row i (boundary 0))
  | chain (i : Fin k) (j : Fin ℓ) (s : Fin (N+L+1)) (r : Fin 5) (hr : r = chainRel N s.val) :
      QueryEdge k N ℓ L r (.row i (.inl (j,s))) (.row i (nxt j s))
  | letter (i : Fin k) (j : Fin ℓ) (t : Fin (L+1)) :
      QueryEdge k N ℓ L 4 (.row i (nxt j ⟨N+t.val,by omega⟩)) (.letter j t)

def query (k N ℓ L : ℕ) : UnaryBinary (QueryVertex k N ℓ L) where
  root v := v = .anchor 0
  binary := QueryEdge k N ℓ L

/-- The target rows are those of the binary construction on the bit strings.
Advance only leaves a block boundary; Begin moves on inside a block. -/
inductive TargetEdge {k : ℕ} (words : Fin k → List Bool) (L : ℕ) :
    Fin 5 → TargetVertex words → TargetVertex words → Prop
  | next (i : Fin k) : TargetEdge words L 0 (.anchor i.castSucc) (.anchor i.succ)
  | begin (i : Fin k) : TargetEdge words L 1 (.anchor i.succ) (.pos i 0)
  | read (i : Fin k) (a b : Fin ((words i).length+1)) (h : b.val = a.val+1)
      (hb : ¬ (L+1) ∣ a.val) : TargetEdge words L 1 (.pos i a) (.pos i b)
  | step (i : Fin k) (a b : Fin ((words i).length+1)) (h : Step a.val b.val) :
      TargetEdge words L 2 (.pos i a) (.pos i b)
  | advance (i : Fin k) (a b : Fin ((words i).length+1)) (h : b.val = a.val+1)
      (hb : (L+1) ∣ a.val) : TargetEdge words L 3 (.pos i a) (.pos i b)
  | letter (i : Fin k) (j : Fin (words i).length) :
      TargetEdge words L 4 (.pos i (occurrence i j)) (.bit ((words i).get j))

def target {k : ℕ} (words : Fin k → List Bool) (L : ℕ) : UnaryBinary (TargetVertex words) where
  root v := v = .anchor 0
  binary := TargetEdge words L

namespace TargetEdge
variable {k L : ℕ} {words : Fin k → List Bool}

theorem next_out {i : Fin k} {v : TargetVertex words}
    (h : TargetEdge words L 0 (.anchor i.castSucc) v) : v = .anchor i.succ := by
  generalize hu : TargetVertex.anchor i.castSucc = u at h
  cases h with
  | next j =>
    have he : i = j := Fin.castSucc_injective k (TargetVertex.anchor.inj hu)
    subst j
    rfl

theorem begin_out {i : Fin k} {v : TargetVertex words}
    (h : TargetEdge words L 1 (.anchor i.succ) v) : v = .pos i 0 := by
  generalize hu : TargetVertex.anchor i.succ = u at h
  cases h with
  | begin j =>
    have he : i = j := Fin.succ_injective k (TargetVertex.anchor.inj hu)
    subst j
    rfl
  | read j a b _ _ => cases hu

theorem read_out {i : Fin k} {a : Fin ((words i).length+1)} {v : TargetVertex words}
    (h : TargetEdge words L 1 (.pos i a) v) : ∃ b, v = .pos i b ∧ b.val = a.val+1 := by
  cases h with
  | read i a b he _ => exact ⟨b,rfl,he⟩

theorem step_out {i : Fin k} {a : Fin ((words i).length+1)} {v : TargetVertex words}
    (h : TargetEdge words L 2 (.pos i a) v) : ∃ b, v = .pos i b ∧ Step a.val b.val := by
  cases h with
  | step i a b he => exact ⟨b,rfl,he⟩

theorem advance_out {i : Fin k} {a : Fin ((words i).length+1)} {v : TargetVertex words}
    (h : TargetEdge words L 3 (.pos i a) v) :
    ∃ b, v = .pos i b ∧ b.val = a.val+1 ∧ (L+1) ∣ a.val := by
  cases h with
  | advance i a b he hb => exact ⟨b,rfl,he,hb⟩

theorem letter_out {i : Fin k} {a : Fin ((words i).length+1)} {v : TargetVertex words}
    (h : TargetEdge words L 4 (.pos i a) v) :
    ∃ j, a = occurrence i j ∧ v = .bit ((words i).get j) := by
  cases h with
  | letter i j => exact ⟨j,rfl,rfl⟩

theorem step_values {i : Fin k} {a b : Fin ((words i).length+1)}
    (h : TargetEdge words L 2 (.pos i a) (.pos i b)) : Step a.val b.val := by
  cases h with
  | step i a b he => exact he

theorem advance_values {i : Fin k} {a b : Fin ((words i).length+1)}
    (h : TargetEdge words L 3 (.pos i a) (.pos i b)) : b.val = a.val+1 ∧ (L+1) ∣ a.val := by
  cases h with
  | advance i a b he hb => exact ⟨he,hb⟩

theorem read_values {i : Fin k} {a b : Fin ((words i).length+1)}
    (h : TargetEdge words L 1 (.pos i a) (.pos i b)) : b.val = a.val+1 := by
  cases h with
  | read i a b he _ => exact he

end TargetEdge

/-- The block-aligned common-subsequence property of bit strings that the
structures decide: `ℓ` letters of `L+1` bits, read from strictly increasing blocks. -/
def BlockCommon {K : Type*} (words : K → List Bool) (L ℓ : ℕ) : Prop :=
  ∃ z : Fin ℓ → Fin (L+1) → Bool, ∀ i, ∃ a : Fin ℓ → ℕ, StrictMono a ∧
    ∀ j t, (words i)[a j * (L+1) + t.val]? = some (z j t)

end TreewidthHom.BlockLCS
