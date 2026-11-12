module

public import TreewidthHom.FiniteEncoding
public import TreewidthHom.IntervalDecomposition

@[expose] public section

namespace TreewidthHom.UnaryBinary

def gaifman {V : Type*} (A : UnaryBinary V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ r, A.binary r u v ∨ A.binary r v u
  symm := ⟨by intro u v ⟨hne,r,h⟩; exact ⟨hne.symm,r,h.elim Or.inr Or.inl⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end TreewidthHom.UnaryBinary

namespace TreewidthHom.LCSInstance

def timeEquiv (N ℓ : ℕ) : Position N ℓ ≃ Fin (ℓ*(N+1)+1) where
  toFun
    | .inl p => (finProdFinEquiv p).castSucc
    | .inr _ => Fin.last _
  invFun := Fin.lastCases (.inr ()) (fun j => .inl (finProdFinEquiv.symm j))
  left_inv := by
    rintro (⟨j,s⟩ | u)
    · simp only [Fin.lastCases_castSucc,Equiv.symm_apply_apply]
    · cases u; simp
  right_inv := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp only [Fin.lastCases_last,Fin.lastCases_castSucc,Equiv.apply_symm_apply]

@[simp] theorem time_block {N ℓ : ℕ} (j : Fin ℓ) (s : Fin (N+1)) :
    (timeEquiv N ℓ (.inl (j,s))).val = s.val+(N+1)*j.val := rfl

@[simp] theorem time_boundary {N ℓ : ℕ} (j : Fin (ℓ+1)) :
    (timeEquiv N ℓ (boundary j)).val = j.val*(N+1) := by
  by_cases h : j.val < ℓ
  · simp [boundary,h,timeEquiv,finProdFinEquiv,Nat.mul_comm]
  · have he : j.val = ℓ := by have := j.isLt; omega
    simp [boundary,timeEquiv,he]

def occurs {k N ℓ : ℕ} : QueryVertex k N ℓ → Fin (ℓ*(N+1)+1) → Prop
  | .anchor _, b => b.val = 0
  | .row _ p, b => b.val = (timeEquiv N ℓ p).val ∨ b.val = (timeEquiv N ℓ p).val+1
  | .letter j, b => b.val = (j.val+1)*(N+1)

instance {k N ℓ : ℕ} (v : QueryVertex k N ℓ) (b : Fin (ℓ*(N+1)+1)) : Decidable (occurs v b) := by
  cases v <;> unfold occurs <;> infer_instance

def queryBag (k N ℓ : ℕ) (b : Fin (ℓ*(N+1)+1)) : Finset (QueryVertex k N ℓ) :=
  Finset.univ.filter (fun v => occurs v b)

@[simp] theorem mem_queryBag {k N ℓ : ℕ} (v : QueryVertex k N ℓ) (b : Fin (ℓ*(N+1)+1)) :
    v ∈ queryBag k N ℓ b ↔ occurs v b := by simp [queryBag]

theorem query_vertex_covered (k N ℓ : ℕ) : ∀ v, ∃ b, v ∈ queryBag k N ℓ b := by
  rintro (a | ⟨i,p⟩ | j)
  · exact ⟨0,by simp [occurs]⟩
  · exact ⟨timeEquiv N ℓ p,by simp [occurs]⟩
  · exact ⟨timeEquiv N ℓ (boundary j.succ),by simp [occurs]⟩

theorem query_edge_covered {k N ℓ : ℕ} {r u v} (h : QueryEdge k N ℓ r u v) :
    ∃ b, u ∈ queryBag k N ℓ b ∧ v ∈ queryBag k N ℓ b := by
  cases h with
  | next i => exact ⟨0,by simp [occurs],by simp [occurs]⟩
  | begin i => exact ⟨0,by simp [occurs],by simp [occurs]⟩
  | step i j s =>
    refine ⟨timeEquiv N ℓ (.inl (j,s.succ)),?_,?_⟩
    · simp [occurs,time_block]; omega
    · simp [occurs]
  | advance i j =>
    refine ⟨timeEquiv N ℓ (boundary j.succ),?_,?_⟩
    · simp only [mem_queryBag,occurs,time_boundary,Fin.val_succ,time_block,Fin.val_last]
      right
      ring
    · simp [occurs]
  | letter i j => exact ⟨timeEquiv N ℓ (boundary j.succ),by simp [occurs],by simp [occurs]⟩

/-- A symmetric sweep of all rows gives a simple width bound 2k.
The written proof uses a finer row-at-a-time sweep to improve this to k+1. -/
noncomputable def queryDecomposition (k N ℓ : ℕ) :
    Decomposition (query k N ℓ).gaifman (SimpleGraph.pathGraph (ℓ*(N+1)+1)) := by
  apply intervalDecomposition _ _ (queryBag k N ℓ) (query_vertex_covered k N ℓ)
  · rintro u v ⟨_,r,h | h⟩
    · exact query_edge_covered h
    · obtain ⟨b,hu,hv⟩ := query_edge_covered h
      exact ⟨b,hv,hu⟩
  · rintro (v | ⟨i,p⟩ | j) a b c hac hcb ha hb <;>
      simp only [mem_queryBag,occurs] at * <;>
      change a.val ≤ c.val at hac <;> change c.val ≤ b.val at hcb <;> omega

theorem query_width (k N ℓ : ℕ) : ∀ b, ((queryDecomposition k N ℓ).bag b).card ≤ 2*k+1 := by
  intro b
  change (queryBag k N ℓ b).card ≤ 2*k+1
  let rows (t : Fin (ℓ*(N+1)+1)) : Finset (QueryVertex k N ℓ) :=
    Finset.univ.image (fun i : Fin k => .row i ((timeEquiv N ℓ).symm t))
  have rows_card : ∀ t, (rows t).card ≤ k := by
    intro t
    exact Finset.card_image_le.trans (by simp)
  by_cases hb : b.val = 0
  · let anchors : Finset (QueryVertex k N ℓ) := Finset.univ.image QueryVertex.anchor
    have hc : anchors.card ≤ k+1 := Finset.card_image_le.trans (by simp)
    have hsub : queryBag k N ℓ b ⊆ anchors ∪ rows 0 := by
      intro v hv
      have h := (mem_queryBag v b).mp hv
      cases v with
      | anchor a => simp [anchors]
      | row i p =>
        have ht : timeEquiv N ℓ p = 0 := by
          apply Fin.ext
          change (timeEquiv N ℓ p).val = 0
          change b.val = _ ∨ b.val = _ at h
          omega
        have hp : p = (timeEquiv N ℓ).symm 0 := (timeEquiv N ℓ).eq_symm_apply.mpr ht
        simp [rows,hp]
      | letter j =>
        change b.val = (j.val+1)*(N+1) at h
        have hz : 0 < (j.val+1)*(N+1) := Nat.mul_pos (by omega) (by omega)
        omega
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le anchors (rows 0)
    have h3 := rows_card 0
    omega
  · let prev : Fin (ℓ*(N+1)+1) := ⟨b.val-1,by have := b.isLt; omega⟩
    let ls : Finset (Fin ℓ) := Finset.univ.filter (fun j => (j.val+1)*(N+1) = b.val)
    let letters : Finset (QueryVertex k N ℓ) := ls.image QueryVertex.letter
    have hl : ls.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      simp only [ls,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
      apply Fin.ext
      have he := Nat.eq_of_mul_eq_mul_right (Nat.succ_pos N) (hi.trans hj.symm)
      omega
    have hl' : letters.card ≤ 1 := Finset.card_image_le.trans hl
    have hsub : queryBag k N ℓ b ⊆ rows b ∪ rows prev ∪ letters := by
      intro v hv
      have h := (mem_queryBag v b).mp hv
      cases v with
      | anchor a => exact False.elim (hb h)
      | row i p =>
        rcases h with h | h
        · have ht : timeEquiv N ℓ p = b := Fin.ext h.symm
          have hp := (timeEquiv N ℓ).eq_symm_apply.mpr ht
          simp [rows,hp]
        · have ht : timeEquiv N ℓ p = prev := by apply Fin.ext; dsimp [prev]; omega
          have hp := (timeEquiv N ℓ).eq_symm_apply.mpr ht
          simp [rows,hp]
      | letter j =>
        change b.val = (j.val+1)*(N+1) at h
        simp [letters,ls,eq_comm,h]
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (rows b ∪ rows prev) letters
    have h3 := Finset.card_union_le (rows b) (rows prev)
    have h4 := rows_card b
    have h5 := rows_card prev
    omega

end TreewidthHom.LCSInstance
