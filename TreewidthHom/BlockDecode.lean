module

public import TreewidthHom.BlockInstance

@[expose] public section

namespace TreewidthHom.BlockLCS
open LCSInstance (Position boundary TargetVertex occurrence boundary_castSucc boundary_last)
namespace Decode
variable {k N ℓ L : ℕ} {words : Fin k → List Bool}
variable (f : UnaryBinary.Hom (query k N ℓ L) (target words L))

theorem anchor_image (i : Fin (k+1)) : f.map (.anchor i) = .anchor i := by
  induction i using Fin.induction with
  | zero => exact f.root (.anchor 0) rfl
  | succ i ih =>
    have h : TargetEdge words L 0 (f.map (.anchor i.castSucc)) (f.map (.anchor i.succ)) :=
      f.binary _ _ _ (.next i)
    rw [ih] at h
    exact TargetEdge.next_out h

theorem initial_image (i : Fin k) : f.map (.row i (boundary 0)) = .pos i 0 := by
  have h : TargetEdge words L 1 (f.map (.anchor i.succ)) (f.map (.row i (boundary 0))) :=
    f.binary _ _ _ (.begin i)
  rw [anchor_image] at h
  exact TargetEdge.begin_out h

/-- Every chain edge leads from a row position to a row position. -/
theorem chain_image (i : Fin k) (j : Fin ℓ) (s : Fin (N+L+1))
    (h : ∃ p, f.map (.row i (.inl (j,s))) = .pos i p) :
    ∃ p, f.map (.row i (nxt j s)) = .pos i p := by
  obtain ⟨p,hp⟩ := h
  have he : TargetEdge words L (chainRel N s.val) (f.map (.row i (.inl (j,s))))
      (f.map (.row i (nxt j s))) := f.binary _ _ _ (.chain i j s _ rfl)
  rw [hp] at he
  rcases Nat.lt_trichotomy s.val N with hs | hs | hs
  · rw [chainRel_step hs] at he
    obtain ⟨q,hq,_⟩ := TargetEdge.step_out he
    exact ⟨q,hq⟩
  · rw [hs,chainRel_advance] at he
    obtain ⟨q,hq,_⟩ := TargetEdge.advance_out he
    exact ⟨q,hq⟩
  · rw [chainRel_read hs] at he
    obtain ⟨q,hq,_⟩ := TargetEdge.read_out he
    exact ⟨q,hq⟩

theorem block_image (i : Fin k) (j : Fin ℓ)
    (hstart : ∃ p, f.map (.row i (boundary j.castSucc)) = .pos i p)
    (s : Fin (N+L+1)) : ∃ p, f.map (.row i (.inl (j,s))) = .pos i p := by
  induction s using Fin.induction with
  | zero => simpa only [boundary_castSucc] using hstart
  | succ s ih =>
    have h := chain_image f i j s.castSucc ih
    rwa [nxt_castSucc] at h

theorem boundary_image (i : Fin k) (j : Fin (ℓ+1)) :
    ∃ p, f.map (.row i (boundary j)) = .pos i p := by
  induction j using Fin.induction with
  | zero => exact ⟨0,initial_image f i⟩
  | succ j ih =>
    have h := chain_image f i j (Fin.last (N+L)) (block_image f i j ih _)
    rwa [nxt_last] at h

theorem row_image (i : Fin k) (p : Position (N+L) ℓ) :
    ∃ q, f.map (.row i p) = .pos i q := by
  rcases p with ⟨j,s⟩ | u
  · exact block_image f i j (boundary_image f i j.castSucc) s
  · cases u
    simpa only [boundary_last] using boundary_image f i (Fin.last ℓ)

variable (c : ∀ i, Position (N+L) ℓ → Fin ((words i).length+1))
variable (hc : ∀ i p, f.map (.row i p) = .pos i (c i p))

include hc in
/-- Positions never decrease along a chain; from the Advance edge on they increase
by exactly one; the Advance edge leaves a block boundary. -/
theorem chain_values (i : Fin k) (j : Fin ℓ) (s : Fin (N+L+1)) :
    (c i (.inl (j,s))).val ≤ (c i (nxt j s)).val ∧
    (N ≤ s.val → (c i (nxt j s)).val = (c i (.inl (j,s))).val+1) ∧
    (s.val = N → (L+1) ∣ (c i (.inl (j,s))).val) := by
  have he : TargetEdge words L (chainRel N s.val) (f.map (.row i (.inl (j,s))))
      (f.map (.row i (nxt j s))) := f.binary _ _ _ (.chain i j s _ rfl)
  rw [hc,hc] at he
  rcases Nat.lt_trichotomy s.val N with hs | hs | hs
  · rw [chainRel_step hs] at he
    have h := step_bounds (TargetEdge.step_values he)
    exact ⟨h.1,fun h' => absurd h' (by omega),fun h' => absurd h' (by omega)⟩
  · rw [hs,chainRel_advance] at he
    have h := TargetEdge.advance_values he
    exact ⟨by omega,fun _ => h.1,fun _ => h.2⟩
  · rw [chainRel_read hs] at he
    have h := TargetEdge.read_values he
    exact ⟨by omega,fun _ => h,fun h' => absurd h' (by omega)⟩

/-- The position at which the query enters the block chosen for letter `j`. -/
def entry (i : Fin k) (j : Fin ℓ) : ℕ := (c i (.inl (j,⟨N,by omega⟩))).val

include hc in
theorem entry_dvd (i : Fin k) (j : Fin ℓ) : (L+1) ∣ entry c i j :=
  (chain_values f c hc i j ⟨N,by omega⟩).2.2 rfl

include hc in
theorem start_le_entry (i : Fin k) (j : Fin ℓ) :
    (c i (boundary j.castSucc)).val ≤ entry c i j := by
  have hm : Monotone (fun s : Fin (N+L+1) => (c i (.inl (j,s))).val) :=
    Fin.monotone_iff_le_succ.mpr (fun s => by
      have h := (chain_values f c hc i j s.castSucc).1
      rwa [nxt_castSucc] at h)
  have h := hm (show (0 : Fin (N+L+1)) ≤ ⟨N,by omega⟩ from Fin.zero_le _)
  rw [boundary_castSucc]
  exact h

include hc in
theorem read_coord (i : Fin k) (j : Fin ℓ) : ∀ (t : ℕ) (ht : t ≤ L),
    (c i (.inl (j,⟨N+t,by omega⟩))).val = entry c i j + t
  | 0, _ => rfl
  | t+1, ht => by
    have ih := read_coord i j t (by omega)
    have h := (chain_values f c hc i j ⟨N+t,by omega⟩).2.1 (by simp)
    have hn : nxt j (⟨N+t,by omega⟩ : Fin (N+L+1)) = .inl (j,⟨N+(t+1),by omega⟩) := by
      unfold nxt
      rw [dite_eq_left (by simp; omega)]
      rfl
    rw [hn,ih] at h
    omega

include hc in
theorem read_nxt (i : Fin k) (j : Fin ℓ) (t : ℕ) (ht : t ≤ L) :
    (c i (nxt j ⟨N+t,by omega⟩)).val = entry c i j + t + 1 := by
  have h := (chain_values f c hc i j ⟨N+t,by omega⟩).2.1 (by simp)
  rw [read_coord f c hc i j t ht] at h
  exact h

include hc in
theorem next_boundary (i : Fin k) (j : Fin ℓ) :
    (c i (boundary j.succ)).val = entry c i j + L + 1 := by
  have h := read_nxt f c hc i j L le_rfl
  have hl : (⟨N+L,by omega⟩ : Fin (N+L+1)) = Fin.last (N+L) := rfl
  rwa [hl,nxt_last] at h

include hc in
theorem entry_strict (i : Fin k) : StrictMono (fun j : Fin ℓ => entry c i j / (L+1)) := by
  have hg : Monotone (fun j : Fin (ℓ+1) => (c i (boundary j)).val) :=
    Fin.monotone_iff_le_succ.mpr (fun j => by
      have h1 := start_le_entry f c hc i j
      have h2 := next_boundary f c hc i j
      omega)
  intro a b hab
  have h1 := hg (show a.succ ≤ b.castSucc by
    change a.val+1 ≤ b.val
    exact hab)
  have h2 := start_le_entry f c hc i b
  have h3 := next_boundary f c hc i a
  dsimp only at h1 ⊢
  have h4 : entry c i a + (L+1) ≤ entry c i b := by omega
  have h5 := Nat.div_le_div_right (c := L+1) h4
  rw [Nat.add_div_right _ (by omega)] at h5
  omega

/-- Every homomorphism of the concrete structures selects block-aligned common letters. -/
theorem blockCommon (f : UnaryBinary.Hom (query k N ℓ L) (target words L)) (hk : 0 < k) :
    BlockCommon words L ℓ := by
  classical
  choose c hc using row_image f
  have letters : ∀ (i : Fin k) (j : Fin ℓ) (t : Fin (L+1)), ∃ m : Fin (words i).length,
      m.val = entry c i j + t.val ∧ f.map (.letter j t) = .bit ((words i).get m) := by
    intro i j t
    have h : TargetEdge words L 4 (f.map (.row i (nxt j ⟨N+t.val,by omega⟩)))
        (f.map (.letter j t)) := f.binary _ _ _ (.letter i j t)
    rw [hc] at h
    obtain ⟨m,hm,hv⟩ := TargetEdge.letter_out h
    refine ⟨m,?_,hv⟩
    have h1 := read_nxt f c hc i j t.val (by have := t.isLt; omega)
    rw [hm] at h1
    simp only [occurrence] at h1
    omega
  choose m hm hletters using letters
  let i0 : Fin k := ⟨0,hk⟩
  refine ⟨fun j t => (words i0).get (m i0 j t),fun i => ?_⟩
  refine ⟨fun j => entry c i j / (L+1),entry_strict f c hc i,fun j t => ?_⟩
  have hd : entry c i j / (L+1) * (L+1) = entry c i j :=
    Nat.div_mul_cancel (entry_dvd f c hc i j)
  rw [hd,← hm i j t,List.getElem?_eq_getElem (m i j t).isLt]
  congr 1
  exact TargetVertex.bit.inj ((hletters i j t).symm.trans (hletters i0 j t))

end Decode
end TreewidthHom.BlockLCS
