module

public import TreewidthHom.BlockInstance

@[expose] public section

namespace TreewidthHom.BlockLCS
open LCSInstance (Position boundary TargetVertex occurrence)

/-- Position after `s` chain moves: stutter from `start` up to the block entry
`ent` during the first `N` moves, then advance one position per move. -/
def tr (N start ent s : ℕ) : ℕ :=
  if s ≤ N then start + min s (ent - start) else ent + (s - N)

theorem tr_zero (N start ent : ℕ) : tr N start ent 0 = start := by simp [tr]

theorem tr_step {N start ent s : ℕ} (h : s < N) :
    Step (tr N start ent s) (tr N start ent (s+1)) := by
  unfold tr Step
  rw [ite_eq_left (by omega : s ≤ N),ite_eq_left (by omega : s+1 ≤ N)]
  omega

theorem tr_late {N start ent s : ℕ} (h1 : start ≤ ent) (h2 : ent ≤ start + N) (hs : N ≤ s) :
    tr N start ent s = ent + (s - N) := by
  unfold tr
  split_ifs <;> omega

theorem tr_le {N start ent s L : ℕ} (h1 : start ≤ ent) (hs : s ≤ N+L+1) :
    tr N start ent s ≤ ent + L + 1 := by
  unfold tr
  split_ifs <;> omega

namespace Encode
variable {k N ℓ L : ℕ} {words : Fin k → List Bool}
variable (a : ∀ _ : Fin k, Fin ℓ → ℕ)

/-- First bit position of the block chosen for letter `j`, counted from zero. -/
def ent (i : Fin k) (j : Fin ℓ) : ℕ := a i j * (L+1)

/-- Sentinel zero, then the position just after each chosen block. -/
def selected (i : Fin k) (j : Fin (ℓ+1)) : ℕ :=
  if h : j.val = 0 then 0 else (a i ⟨j.val-1,by have := j.isLt; omega⟩ + 1) * (L+1)

@[simp] theorem selected_zero (i : Fin k) : selected (L := L) a i 0 = 0 := by simp [selected]

theorem selected_succ (i : Fin k) (j : Fin ℓ) :
    selected (L := L) a i j.succ = ent (L := L) a i j + (L+1) := by
  simp [selected,ent,Nat.succ_mul]

theorem start_le_ent (ha : ∀ i, StrictMono (a i)) (i : Fin k) (j : Fin ℓ) :
    selected (L := L) a i j.castSucc ≤ ent (L := L) a i j := by
  unfold selected ent
  split
  · omega
  · rename_i h
    have hj : (⟨j.castSucc.val-1,by have := j.isLt; omega⟩ : Fin ℓ) < j := by
      change j.val-1 < j.val
      simp only [Fin.val_castSucc] at h
      omega
    exact Nat.mul_le_mul_right _ (ha i hj)

variable (z : Fin ℓ → Fin (L+1) → Bool)

theorem bit_lt (hz : ∀ i j t, (words i)[a i j * (L+1) + t.val]? = some (z j t))
    (i : Fin k) (j : Fin ℓ) (t : Fin (L+1)) :
    ent (L := L) a i j + t.val < (words i).length := by
  obtain ⟨h,_⟩ := List.getElem?_eq_some_iff.mp (hz i j t)
  exact h

theorem ent_bound (hz : ∀ i j t, (words i)[a i j * (L+1) + t.val]? = some (z j t))
    (i : Fin k) (j : Fin ℓ) : ent (L := L) a i j + L + 1 ≤ (words i).length := by
  have h := bit_lt a z hz i j (Fin.last L)
  simp only [Fin.val_last] at h
  omega

theorem selected_bound (hz : ∀ i j t, (words i)[a i j * (L+1) + t.val]? = some (z j t))
    (i : Fin k) (j : Fin (ℓ+1)) : selected (L := L) a i j ≤ (words i).length := by
  induction j using Fin.cases with
  | zero => simp
  | succ j =>
    rw [selected_succ]
    have := ent_bound a z hz i j
    omega

/-- The target position of every query row vertex. -/
def coordinate (ha : ∀ i, StrictMono (a i))
    (hz : ∀ i j t, (words i)[a i j * (L+1) + t.val]? = some (z j t))
    (i : Fin k) : Position (N+L) ℓ → Fin ((words i).length+1)
  | .inl (j,s) => ⟨tr N (selected (L := L) a i j.castSucc) (ent (L := L) a i j) s.val,by
      have h1 := tr_le (N := N) (L := L) (start_le_ent (L := L) a ha i j)
        (show s.val ≤ N+L+1 by omega)
      have h2 := ent_bound a z hz i j
      omega⟩
  | .inr _ => ⟨selected (L := L) a i (Fin.last ℓ),by
      have := selected_bound a z hz i (Fin.last ℓ); omega⟩

variable (ha : ∀ i, StrictMono (a i))
variable (hz : ∀ i j t, (words i)[a i j * (L+1) + t.val]? = some (z j t))

theorem coordinate_boundary (i : Fin k) (j : Fin (ℓ+1)) :
    (coordinate (N := N) a z ha hz i (boundary j)).val = selected (L := L) a i j := by
  by_cases hj : j.val < ℓ
  · have he : (⟨j.val,hj⟩ : Fin ℓ).castSucc = j := by ext; rfl
    simp only [boundary,dite_eq_left hj,coordinate,Fin.val_zero,tr_zero,he]
  · have he : j = Fin.last ℓ := by ext; have := j.isLt; simp; omega
    subst j
    simp [boundary,coordinate]

theorem coordinate_nxt (hN : ∀ i, (words i).length ≤ N) (i : Fin k) (j : Fin ℓ)
    (s : Fin (N+L+1)) (hs : N ≤ s.val) :
    (coordinate (N := N) a z ha hz i (nxt j s)).val =
      ent (L := L) a i j + (s.val - N) + 1 := by
  have h1 := start_le_ent (L := L) a ha i j
  have h2 := ent_bound a z hz i j
  have h3 := hN i
  unfold nxt
  split
  · rename_i h
    change tr N _ _ (s.val+1) = _
    rw [tr_late h1 (by omega) (by omega)]
    omega
  · rw [coordinate_boundary,selected_succ]
    have := s.isLt
    omega

theorem coordinate_chain (hN : ∀ i, (words i).length ≤ N) (i : Fin k) (j : Fin ℓ)
    (s : Fin (N+L+1)) (hs : N ≤ s.val) :
    (coordinate (N := N) a z ha hz i (.inl (j,s))).val = ent (L := L) a i j + (s.val - N) := by
  have h1 := start_le_ent (L := L) a ha i j
  have h2 := ent_bound a z hz i j
  have h3 := hN i
  change tr N _ _ s.val = _
  exact tr_late h1 (by omega) hs

def vertexMap : QueryVertex k N ℓ L → TargetVertex words
  | .anchor i => .anchor i
  | .row i p => .pos i (coordinate a z ha hz i p)
  | .letter j t => .bit (z j t)

/-- Block-aligned common letters supply a homomorphism of the concrete structures. -/
def hom (hN : ∀ i, (words i).length ≤ N) :
    UnaryBinary.Hom (query k N ℓ L) (target words L) where
  map := vertexMap a z ha hz
  root := by intro v hv; change v = .anchor 0 at hv; subst v; rfl
  binary := by
    intro r u v h
    cases h with
    | next i => exact .next i
    | begin i =>
      change TargetEdge words L 1 (.anchor i.succ) (.pos i (coordinate a z ha hz i (boundary 0)))
      have he : coordinate (N := N) a z ha hz i (boundary 0) = 0 := by
        apply Fin.ext
        simp [coordinate_boundary]
      rw [he]
      exact .begin i
    | chain i j s r hr =>
      subst hr
      change TargetEdge words L _ (.pos i (coordinate a z ha hz i (.inl (j,s))))
        (.pos i (coordinate a z ha hz i (nxt j s)))
      rcases Nat.lt_trichotomy s.val N with hs | hs | hs
      · rw [chainRel_step hs]
        apply TargetEdge.step
        have hn : nxt j s = .inl (j,⟨s.val+1,by omega⟩) := by
          unfold nxt
          rw [dite_eq_left (by omega : s.val < N+L)]
        rw [hn]
        exact tr_step hs
      · rw [hs,chainRel_advance]
        apply TargetEdge.advance
        · rw [coordinate_nxt a z ha hz hN i j s (by omega),
            coordinate_chain a z ha hz hN i j s (by omega)]
        · rw [coordinate_chain a z ha hz hN i j s (by omega),hs,Nat.sub_self,Nat.add_zero]
          exact Dvd.intro_left _ rfl
      · rw [chainRel_read hs]
        apply TargetEdge.read
        · rw [coordinate_nxt a z ha hz hN i j s (by omega),
            coordinate_chain a z ha hz hN i j s (by omega)]
        · rw [coordinate_chain a z ha hz hN i j s (by omega)]
          intro hd
          have hd' : (L+1) ∣ s.val - N :=
            (Nat.dvd_add_right (Dvd.intro_left _ rfl)).mp hd
          have := Nat.le_of_dvd (by omega) hd'
          have := s.isLt
          omega
    | letter i j t =>
      change TargetEdge words L 4
        (.pos i (coordinate a z ha hz i (nxt j ⟨N+t.val,by omega⟩))) (.bit (z j t))
      obtain ⟨h,hv⟩ := List.getElem?_eq_some_iff.mp (hz i j t)
      have he : coordinate (N := N) a z ha hz i (nxt j ⟨N+t.val,by omega⟩) =
          occurrence i ⟨a i j * (L+1) + t.val,h⟩ := by
        apply Fin.ext
        rw [coordinate_nxt a z ha hz hN i j _ (by simp)]
        simp [occurrence,ent]
      rw [he,← hv]
      exact .letter i ⟨a i j * (L+1) + t.val,h⟩

end Encode

/-- Forward correctness for every length, including the empty subsequence. -/
theorem blockCommon_hom {k N ℓ L : ℕ} {words : Fin k → List Bool}
    (hN : ∀ i, (words i).length ≤ N) (h : BlockCommon words L ℓ) :
    Nonempty (UnaryBinary.Hom (query k N ℓ L) (target words L)) := by
  obtain ⟨z,hz⟩ := h
  choose a ha hz using hz
  exact ⟨Encode.hom a z ha hz hN⟩

end TreewidthHom.BlockLCS
