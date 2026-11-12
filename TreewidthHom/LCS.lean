module

public import TreewidthHom.PaddedSteps

@[expose] public section

/-! # Common subsequences and the padded position constraints -/
namespace TreewidthHom

/-- The standard list-theoretic decision problem, with Boolean alphabet. -/
def CommonSubsequence {K : Type*} (words : K → List Bool) (ℓ : ℕ) : Prop :=
  ∃ z : List Bool, z.length = ℓ ∧ ∀ i, z.Sublist (words i)

/-- Increasing position selections in each input word, sharing the same letters. -/
def CommonEmbedding {K : Type*} (words : K → List Bool) (ℓ : ℕ) : Prop :=
  ∃ z : Fin ℓ → Bool, ∀ i, ∃ e : Fin ℓ ↪o Fin (words i).length,
    ∀ j, z j = (words i).get (e j)

theorem commonSubsequence_iff_embedding {K : Type*} (words : K → List Bool) (ℓ : ℕ) :
    CommonSubsequence words ℓ ↔ CommonEmbedding words ℓ := by
  constructor
  · rintro ⟨z, rfl, hz⟩
    refine ⟨z.get, fun i => ?_⟩
    exact List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp (hz i)
  · rintro ⟨z, hz⟩
    refine ⟨List.ofFn z, by simp, fun i => ?_⟩
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    obtain ⟨e, he⟩ := hz i
    let e' : Fin (List.ofFn z).length ↪o Fin (words i).length :=
      (Fin.castOrderIso (List.length_ofFn)).toOrderEmbedding.comp e
    refine ⟨e', fun j => ?_⟩
    simpa [e', Fin.cast] using he (Fin.cast (List.length_ofFn) j)


/-- The local constraints of the query's padded row blocks. Selected positions
are zero-based; the row sentinel is position zero, so selected endpoints use +1. -/
def PaddedSelection {K : Type*} (words : K → List Bool) (N ℓ : ℕ) : Prop :=
  ∃ z : Fin ℓ → Bool, ∃ pos : ∀ i, Fin ℓ → Fin (words i).length,
    (∀ i j, z j = (words i).get (pos i j)) ∧
    (∀ i (h : 0 < ℓ), PaddedAdvance N 0 ((pos i ⟨0, h⟩).val + 1)) ∧
    (∀ i (j : ℕ) (h : j + 1 < ℓ),
      PaddedAdvance N ((pos i ⟨j, by omega⟩).val + 1)
        ((pos i ⟨j + 1, h⟩).val + 1))

/-- The position constraints used in the reduction express exactly LCS.
The input-size bound N need not be tight. This does not yet identify these
constraints with a homomorphism of the full untyped graph construction. -/
theorem commonSubsequence_iff_paddedSelection {K : Type*}
    (words : K → List Bool) (N ℓ : ℕ) (hN : ∀ i, (words i).length ≤ N) :
    CommonSubsequence words ℓ ↔ PaddedSelection words N ℓ := by
  rw [commonSubsequence_iff_embedding]
  constructor
  · rintro ⟨z, hz⟩
    choose e he using hz
    refine ⟨z, fun i => e i, he, ?_, ?_⟩
    · intro i h
      apply paddedAdvance_iff.mpr
      have hp := (e i ⟨0, h⟩).isLt
      have hb := hN i
      omega
    · intro i j h
      dsimp only
      apply paddedAdvance_iff.mpr
      have hs := (e i).strictMono (show (⟨j, by omega⟩ : Fin ℓ) < ⟨j+1,h⟩ by simp)
      have hp := (e i ⟨j + 1, h⟩).isLt
      have hb := hN i
      change (e i ⟨j, by omega⟩).val < (e i ⟨j + 1, h⟩).val at hs
      omega
  · rintro ⟨z, pos, hletters, _hfirst, hnext⟩
    refine ⟨z, fun i => ?_⟩
    have hmono : StrictMono (pos i) := by
      cases ℓ with
      | zero => intro j; exact Fin.elim0 j
      | succ l =>
        apply Fin.strictMono_iff_lt_succ.mpr
        intro j
        have hs := paddedAdvance_strict (hnext i j.val (by omega))
        change (pos i j.castSucc).val < (pos i j.succ).val
        have h0 : (⟨j.val, by omega⟩ : Fin (l+1)) = j.castSucc := by ext; rfl
        have h1 : (⟨j.val + 1, by omega⟩ : Fin (l+1)) = j.succ := by ext; rfl
        rw [h0, h1] at hs
        omega
    exact ⟨OrderEmbedding.ofStrictMono (pos i) hmono, hletters i⟩

end TreewidthHom
