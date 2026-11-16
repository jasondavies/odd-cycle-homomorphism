module

public import TreewidthHom.BlockInstance
public import TreewidthHom.ReductionSize

@[expose] public section

/-! # Width and size of the block-encoded LCS structures -/
namespace TreewidthHom.BlockLCS
open LCSInstance (Position boundary TargetVertex occurrence timeEquiv time_block time_boundary)

def queryEquiv (k N ℓ L : ℕ) :
    QueryVertex k N ℓ L ≃ (Fin (k+1) ⊕ ((Fin k × Position (N+L) ℓ) ⊕ (Fin ℓ × Fin (L+1)))) where
  toFun
    | .anchor i => .inl i
    | .row i p => .inr (.inl (i,p))
    | .letter j t => .inr (.inr (j,t))
  invFun
    | .inl i => .anchor i
    | .inr (.inl (i,p)) => .row i p
    | .inr (.inr (j,t)) => .letter j t
  left_inv := by intro v; cases v <;> rfl
  right_inv := by rintro (i | ⟨i,p⟩ | ⟨j,t⟩) <;> rfl

instance queryFintype (k N ℓ L : ℕ) : Fintype (QueryVertex k N ℓ L) :=
  Fintype.ofEquiv _ (queryEquiv k N ℓ L).symm

theorem query_card (k N ℓ L : ℕ) :
    Fintype.card (QueryVertex k N ℓ L) = (k+1) + k*(ℓ*(N+L+1)+1) + ℓ*(L+1) := by
  rw [Fintype.card_congr (queryEquiv k N ℓ L)]
  simp [Position,Fintype.card_sum,Fintype.card_prod,Nat.add_assoc]

/-- Each chain edge advances the sweep time by one. -/
theorem time_nxt {M ℓ : ℕ} (j : Fin ℓ) (s : Fin (M+1)) :
    (timeEquiv M ℓ (nxt j s)).val = s.val+(M+1)*j.val+1 := by
  unfold nxt
  split
  · rw [time_block]
    dsimp only
    omega
  · rw [time_boundary]
    have hs : s.val = M := by have := s.isLt; omega
    simp only [Fin.val_succ,hs,Nat.succ_mul,Nat.mul_comm (M+1)]
    omega

/-- The single sweep time at which a shared bit variable is needed. -/
def letterTime (N L j t : ℕ) : ℕ := N+t+(N+L+1)*j+1

theorem letterTime_inj {N L j j' t t' : ℕ} (ht : t ≤ L) (ht' : t' ≤ L)
    (h : letterTime N L j t = letterTime N L j' t') : j = j' ∧ t = t' := by
  unfold letterTime at h
  have h1 : (N+t+(N+L+1)*j)/(N+L+1) = j := by
    rw [Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt (by omega),zero_add]
  have h2 : (N+t'+(N+L+1)*j')/(N+L+1) = j' := by
    rw [Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt (by omega),zero_add]
  have h3 : N+t+(N+L+1)*j = N+t'+(N+L+1)*j' := by omega
  have hj : j = j' := by rw [← h1,← h2,h3]
  subst hj
  exact ⟨rfl,by omega⟩

def occurs {k N ℓ L : ℕ} : QueryVertex k N ℓ L → Fin (ℓ*(N+L+1)+1) → Prop
  | .anchor _, b => b.val = 0
  | .row _ p, b => b.val = (timeEquiv (N+L) ℓ p).val ∨ b.val = (timeEquiv (N+L) ℓ p).val+1
  | .letter j t, b => b.val = letterTime N L j.val t.val

instance {k N ℓ L : ℕ} (v : QueryVertex k N ℓ L) (b : Fin (ℓ*(N+L+1)+1)) :
    Decidable (occurs v b) := by
  cases v <;> unfold occurs <;> infer_instance

def queryBag (k N ℓ L : ℕ) (b : Fin (ℓ*(N+L+1)+1)) : Finset (QueryVertex k N ℓ L) :=
  Finset.univ.filter (fun v => occurs v b)

@[simp] theorem mem_queryBag {k N ℓ L : ℕ} (v : QueryVertex k N ℓ L) (b : Fin (ℓ*(N+L+1)+1)) :
    v ∈ queryBag k N ℓ L b ↔ occurs v b := by simp [queryBag]

theorem letter_time {N ℓ L : ℕ} (j : Fin ℓ) (t : Fin (L+1)) :
    (timeEquiv (N+L) ℓ (nxt j ⟨N+t.val,by omega⟩)).val = letterTime N L j.val t.val := by
  rw [time_nxt]
  rfl

theorem query_vertex_covered (k N ℓ L : ℕ) : ∀ v, ∃ b, v ∈ queryBag k N ℓ L b := by
  rintro (a | ⟨i,p⟩ | ⟨j,t⟩)
  · exact ⟨0,by simp [occurs]⟩
  · exact ⟨timeEquiv (N+L) ℓ p,by simp [occurs]⟩
  · exact ⟨timeEquiv (N+L) ℓ (nxt j ⟨N+t.val,by omega⟩),by simp [occurs,letter_time]⟩

theorem query_edge_covered {k N ℓ L : ℕ} {r u v} (h : QueryEdge k N ℓ L r u v) :
    ∃ b, u ∈ queryBag k N ℓ L b ∧ v ∈ queryBag k N ℓ L b := by
  cases h with
  | next i => exact ⟨0,by simp [occurs],by simp [occurs]⟩
  | begin i => exact ⟨0,by simp [occurs],by simp [occurs]⟩
  | chain i j s r hr =>
    refine ⟨timeEquiv (N+L) ℓ (nxt j s),?_,?_⟩
    · simp only [mem_queryBag,occurs,time_nxt,time_block]
      right
      trivial
    · simp [occurs]
  | letter i j t =>
    exact ⟨timeEquiv (N+L) ℓ (nxt j ⟨N+t.val,by omega⟩),by simp [occurs],
      by simp [occurs,letter_time]⟩

/-- A symmetric sweep of all rows. Every bit variable is needed at one time only. -/
noncomputable def queryDecomposition (k N ℓ L : ℕ) :
    Decomposition (query k N ℓ L).gaifman (SimpleGraph.pathGraph (ℓ*(N+L+1)+1)) := by
  apply intervalDecomposition _ _ (queryBag k N ℓ L) (query_vertex_covered k N ℓ L)
  · rintro u v ⟨_,r,h | h⟩
    · exact query_edge_covered h
    · obtain ⟨b,hu,hv⟩ := query_edge_covered h
      exact ⟨b,hv,hu⟩
  · rintro (v | ⟨i,p⟩ | ⟨j,t⟩) a b c hac hcb ha hb <;>
      simp only [mem_queryBag,occurs] at * <;>
      change a.val ≤ c.val at hac <;> change c.val ≤ b.val at hcb <;> omega

theorem query_width (k N ℓ L : ℕ) :
    ∀ b, ((queryDecomposition k N ℓ L).bag b).card ≤ 2*k+1 := by
  intro b
  change (queryBag k N ℓ L b).card ≤ 2*k+1
  let rows (t : Fin (ℓ*(N+L+1)+1)) : Finset (QueryVertex k N ℓ L) :=
    Finset.univ.image (fun i : Fin k => .row i ((timeEquiv (N+L) ℓ).symm t))
  have rows_card : ∀ t, (rows t).card ≤ k := by
    intro t
    exact Finset.card_image_le.trans (by simp)
  by_cases hb : b.val = 0
  · let anchors : Finset (QueryVertex k N ℓ L) := Finset.univ.image QueryVertex.anchor
    have hc : anchors.card ≤ k+1 := Finset.card_image_le.trans (by simp)
    have hsub : queryBag k N ℓ L b ⊆ anchors ∪ rows 0 := by
      intro v hv
      have h := (mem_queryBag v b).mp hv
      cases v with
      | anchor a => simp [anchors]
      | row i p =>
        have ht : timeEquiv (N+L) ℓ p = 0 := by
          apply Fin.ext
          change (timeEquiv (N+L) ℓ p).val = 0
          change b.val = _ ∨ b.val = _ at h
          omega
        have hp : p = (timeEquiv (N+L) ℓ).symm 0 := (timeEquiv (N+L) ℓ).eq_symm_apply.mpr ht
        simp [rows,hp]
      | letter j t =>
        change b.val = letterTime N L j.val t.val at h
        unfold letterTime at h
        omega
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le anchors (rows 0)
    have h3 := rows_card 0
    omega
  · let prev : Fin (ℓ*(N+L+1)+1) := ⟨b.val-1,by have := b.isLt; omega⟩
    let ls : Finset (Fin ℓ × Fin (L+1)) :=
      Finset.univ.filter (fun p => letterTime N L p.1.val p.2.val = b.val)
    let letters : Finset (QueryVertex k N ℓ L) := ls.image (fun p => .letter p.1 p.2)
    have hl : ls.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p hp q hq
      simp only [ls,Finset.mem_filter,Finset.mem_univ,true_and] at hp hq
      have h := letterTime_inj (by have := p.2.isLt; omega) (by have := q.2.isLt; omega)
        (hp.trans hq.symm)
      exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
    have hl' : letters.card ≤ 1 := Finset.card_image_le.trans hl
    have hsub : queryBag k N ℓ L b ⊆ rows b ∪ rows prev ∪ letters := by
      intro v hv
      have h := (mem_queryBag v b).mp hv
      cases v with
      | anchor a => exact False.elim (hb h)
      | row i p =>
        rcases h with h | h
        · have ht : timeEquiv (N+L) ℓ p = b := Fin.ext h.symm
          have hp := (timeEquiv (N+L) ℓ).eq_symm_apply.mpr ht
          simp [rows,hp]
        · have ht : timeEquiv (N+L) ℓ p = prev := by apply Fin.ext; dsimp [prev]; omega
          have hp := (timeEquiv (N+L) ℓ).eq_symm_apply.mpr ht
          simp [rows,hp]
      | letter j t =>
        change b.val = letterTime N L j.val t.val at h
        have hm : (j,t) ∈ ls := by simp [ls,h]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(j,t),hm,rfl⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (rows b ∪ rows prev) letters
    have h3 := Finset.card_union_le (rows b) (rows prev)
    have h4 := rows_card b
    have h5 := rows_card prev
    omega

/-- Every fact of the block target lies on an edge of the binary target. -/
theorem edge_binary {k L : ℕ} {words : Fin k → List Bool} {r : Fin 5}
    {u v : TargetVertex words} (h : TargetEdge words L r u v) :
    ∃ r', LCSInstance.TargetEdge words r' u v := by
  cases h with
  | next i => exact ⟨0,.next i⟩
  | begin i => exact ⟨1,.begin i⟩
  | read i a b he _ => exact ⟨3,.advance i a b he⟩
  | step i a b he => exact ⟨2,.step i a b he⟩
  | advance i a b he _ => exact ⟨3,.advance i a b he⟩
  | letter i j => exact ⟨4,.letter i j⟩

theorem gaifman_le {k : ℕ} (words : Fin k → List Bool) (L : ℕ) :
    (target words L).gaifman ≤ (LCSInstance.target words).gaifman := by
  rintro u v ⟨hne,r,h | h⟩
  · obtain ⟨r',h'⟩ := edge_binary h
    exact ⟨hne,r',Or.inl h'⟩
  · obtain ⟨r',h'⟩ := edge_binary h
    exact ⟨hne,r',Or.inr h'⟩

/-- The block target has the Gaifman graph of a binary target, hence width three. -/
theorem target_width {k : ℕ} (words : Fin k → List Bool) (L : ℕ) :
    ∃ B : Type, ∃ T : SimpleGraph B, ∃ D : Decomposition (target words L).gaifman T,
      ∀ b, (D.bag b).card ≤ 4 := by
  obtain ⟨B,T,D,hw⟩ := LCSInstance.target_width words
  exact ⟨B,T,D.mono _ (gaifman_le words L),hw⟩

theorem query_domain_bound {k N ℓ L s : ℕ} (hk : k ≤ s) (hN : N ≤ s) (hℓ : ℓ ≤ s)
    (hL : L ≤ s) (hℓL : ℓ*(L+1) ≤ s) :
    Fintype.card (QueryVertex k N ℓ L) + 1 ≤ 8*(s+1)^3 := by
  rw [query_card]
  have h1 : ℓ*(N+L+1) ≤ (s+1)*(2*(s+1)) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : k*(ℓ*(N+L+1)+1) ≤ (s+1)*((s+1)*(2*(s+1))+1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : s+1 ≤ (s+1)^3 := by
    calc
      s+1 = (s+1)^1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

end TreewidthHom.BlockLCS
