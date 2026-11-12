module

public import TreewidthHom.LCSInstance

@[expose] public section

namespace TreewidthHom.LCSInstance
namespace Decode
variable {k N ℓ : ℕ} {words : Fin k → List Bool}
variable (f : UnaryBinary.Hom (query k N ℓ) (target words))

theorem anchor_image (i : Fin (k+1)) : f.map (.anchor i) = .anchor i := by
  induction i using Fin.induction with
  | zero => exact f.root (.anchor 0) rfl
  | succ i ih =>
    have h : TargetEdge words 0 (f.map (.anchor i.castSucc)) (f.map (.anchor i.succ)) :=
      f.binary _ _ _ (.next i)
    rw [ih] at h
    exact TargetEdge.next_out h

theorem initial_image (i : Fin k) : f.map (.row i (boundary 0)) = .pos i 0 := by
  have h : TargetEdge words 1 (f.map (.anchor i.succ)) (f.map (.row i (boundary 0))) :=
    f.binary _ _ _ (.begin i)
  rw [anchor_image] at h
  exact TargetEdge.begin_out h

theorem block_image (i : Fin k) (j : Fin ℓ)
    (hstart : ∃ p, f.map (.row i (boundary j.castSucc)) = .pos i p)
    (s : Fin (N+1)) : ∃ p, f.map (.row i (.inl (j,s))) = .pos i p := by
  induction s using Fin.induction with
  | zero => simpa only [boundary_castSucc] using hstart
  | succ s ih =>
    obtain ⟨p,hp⟩ := ih
    have h : TargetEdge words 2 (f.map (.row i (.inl (j,s.castSucc))))
        (f.map (.row i (.inl (j,s.succ)))) := f.binary _ _ _ (.step i j s)
    rw [hp] at h
    obtain ⟨q,hq,_⟩ := TargetEdge.step_out h
    exact ⟨q,hq⟩

theorem boundary_image (i : Fin k) (j : Fin (ℓ+1)) :
    ∃ p, f.map (.row i (boundary j)) = .pos i p := by
  induction j using Fin.induction with
  | zero => exact ⟨0,initial_image f i⟩
  | succ j ih =>
    obtain ⟨p,hp⟩ := block_image f i j ih (Fin.last N)
    have h : TargetEdge words 3 (f.map (.row i (.inl (j,Fin.last N))))
        (f.map (.row i (boundary j.succ))) := f.binary _ _ _ (.advance i j)
    rw [hp] at h
    obtain ⟨q,hq,_⟩ := TargetEdge.advance_out h
    exact ⟨q,hq⟩

theorem row_image (i : Fin k) (p : Position N ℓ) :
    ∃ q, f.map (.row i p) = .pos i q := by
  rcases p with ⟨j,s⟩ | u
  · exact block_image f i j (boundary_image f i j.castSucc) s
  · cases u
    simpa only [boundary_last] using boundary_image f i (Fin.last ℓ)

/-- Any legal row assignment strictly increases across each padded block. -/
theorem block_strict (c : ∀ i, Position N ℓ → Fin ((words i).length+1))
    (hc : ∀ i p, f.map (.row i p) = .pos i (c i p)) (i : Fin k) (j : Fin ℓ) :
    (c i (boundary j.castSucc)).val < (c i (boundary j.succ)).val := by
  have hs : ∀ s : Fin N,
      Step (c i (.inl (j,s.castSucc))).val (c i (.inl (j,s.succ))).val := by
    intro s
    apply TargetEdge.step_values
    have h := f.binary _ _ _ (QueryEdge.step i j s)
    change TargetEdge words 2 _ _ at h
    simpa only [hc] using h
  have hm : Monotone (fun s : Fin (N+1) => (c i (.inl (j,s))).val) :=
    Fin.monotone_iff_le_succ.mpr (fun s => (step_bounds (hs s)).1)
  have hb := hm (show (0 : Fin (N+1)) ≤ Fin.last N by exact Fin.zero_le _)
  have ha : (c i (boundary j.succ)).val = (c i (.inl (j,Fin.last N))).val + 1 := by
    apply TargetEdge.advance_values
    have h := f.binary _ _ _ (QueryEdge.advance i j)
    change TargetEdge words 3 _ _ at h
    simpa only [hc] using h
  rw [boundary_castSucc]
  dsimp only at hb
  omega

/-- Every homomorphism of the concrete structures determines a common subsequence. -/
theorem commonSubsequence (f : UnaryBinary.Hom (query k N ℓ) (target words)) (hk : 0 < k) : TreewidthHom.CommonSubsequence words ℓ := by
  classical
  rw [commonSubsequence_iff_embedding]
  choose c hc using row_image f
  have letters : ∀ i : Fin k, ∀ j : Fin ℓ, ∃ e : Fin (words i).length,
      c i (boundary j.succ) = occurrence i e ∧
      f.map (.letter j) = .bit ((words i).get e) := by
    intro i j
    have h : TargetEdge words 4 (f.map (.row i (boundary j.succ))) (f.map (.letter j)) :=
      f.binary _ _ _ (.letter i j)
    rw [hc] at h
    exact TargetEdge.letter_out h
  choose e he hletters using letters
  let i0 : Fin k := ⟨0,hk⟩
  let z : Fin ℓ → Bool := fun j => (words i0).get (e i0 j)
  refine ⟨z,fun i => ?_⟩
  have hm : StrictMono (fun j : Fin (ℓ+1) => (c i (boundary j)).val) :=
    Fin.strictMono_iff_lt_succ.mpr (fun j => block_strict f c hc i j)
  have hmono : StrictMono (e i) := by
    intro a b hab
    have h := hm (show a.succ < b.succ by simpa using hab)
    dsimp only at h
    rw [he i a, he i b] at h
    change (e i a).val < (e i b).val
    simpa only [occurrence, Nat.add_lt_add_iff_right] using h
  refine ⟨OrderEmbedding.ofStrictMono (e i) hmono, fun j => ?_⟩
  exact TargetVertex.bit.inj ((hletters i0 j).symm.trans (hletters i j))

end Decode
end TreewidthHom.LCSInstance
