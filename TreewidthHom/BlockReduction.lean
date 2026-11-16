module

public import TreewidthHom.BlockEncode
public import TreewidthHom.BlockDecode
public import TreewidthHom.BlockWidth
public import TreewidthHom.FullReduction

@[expose] public section

/-!
# The reduction from LCS over an arbitrary alphabet

Letters are vectors of `L+1` bits. The main theorem `full_reduction` has the same
form as `LCSInstance.full_reduction`, for words over the alphabet `Fin (L+1) → Bool`.
`alphabet_reduction` transfers it to any finite alphabet through an injective code.
-/
namespace TreewidthHom.BlockLCS
open LCSInstance (TargetVertex totalLength dataSize word_le_total)

/-- Correctness of the block-encoded relational structures, for all lengths and
all numbers of strings (including zero). -/
theorem block_relational_iff {k N ℓ L : ℕ} (words : Fin k → List Bool)
    (hN : ∀ i, (words i).length ≤ N) :
    Nonempty (UnaryBinary.Hom (query k N ℓ L) (target words L)) ↔ BlockCommon words L ℓ := by
  constructor
  · rintro ⟨f⟩
    by_cases hk : 0 < k
    · exact Decode.blockCommon f hk
    · have he : k = 0 := by omega
      subst k
      exact ⟨fun _ _ => false,fun i => Fin.elim0 i⟩
  · exact blockCommon_hom hN

/-- The final simple undirected source graph. -/
noncomputable def sourceGraph (k N ℓ L : ℕ) :=
  (query k N ℓ L).asRelational.untypedGraph schemaMarkers

/-- The final simple undirected target graph. -/
noncomputable def targetGraph {k : ℕ} (words : Fin k → List Bool) (L : ℕ) :=
  (target words L).asRelational.untypedGraph schemaMarkers

theorem block_graph_iff {k N ℓ L : ℕ} (words : Fin k → List Bool)
    (hN : ∀ i, (words i).length ≤ N) :
    Nonempty (sourceGraph k N ℓ L →g targetGraph words L) ↔ BlockCommon words L ℓ := by
  unfold sourceGraph targetGraph
  rw [Relational.relationalReduction_iff,← UnaryBinary.hom_iff_relational]
  exact block_relational_iff words hN

theorem source_width (k N ℓ L : ℕ) : HasWidth (sourceGraph k N ℓ L) (max (2*k) 3) := by
  classical
  exact (query k N ℓ L).untyped_width
    ⟨inferInstance,_,_,queryDecomposition k N ℓ L,query_width k N ℓ L⟩

theorem final_target_width {k : ℕ} (words : Fin k → List Bool) (L : ℕ) :
    HasWidth (targetGraph words L) 3 := by
  obtain ⟨B,T,D,hw⟩ := target_width words L
  have h : HasWidth (target words L).gaifman 3 := ⟨inferInstance,B,T,D,hw⟩
  exact (target words L).untyped_width h

/-! ## Letters as bit blocks -/

/-- Concatenate the bit blocks of a word of letters. -/
def bits {L : ℕ} (w : List (Fin (L+1) → Bool)) : List Bool := w.flatMap List.ofFn

theorem bits_cons {L : ℕ} (c : Fin (L+1) → Bool) (w : List (Fin (L+1) → Bool)) :
    bits (c :: w) = List.ofFn c ++ bits w := by simp [bits]

theorem bits_length {L : ℕ} (w : List (Fin (L+1) → Bool)) :
    (bits w).length = w.length*(L+1) := by
  induction w with
  | nil => simp [bits]
  | cons c w ih =>
    rw [bits_cons,List.length_append,ih,List.length_ofFn,List.length_cons,Nat.succ_mul]
    omega

/-- Bit `t` of block `a` is bit `t` of letter `a`. -/
theorem bits_getElem? {L : ℕ} (w : List (Fin (L+1) → Bool)) (a : ℕ) (t : Fin (L+1)) :
    (bits w)[a*(L+1)+t.val]? = w[a]?.map (fun c => c t) := by
  induction w generalizing a with
  | nil => simp [bits]
  | cons c w ih =>
    rw [bits_cons]
    cases a with
    | zero =>
      rw [Nat.zero_mul,Nat.zero_add,
        List.getElem?_append_left (by rw [List.length_ofFn]; exact t.isLt),
        List.getElem?_ofFn,dite_eq_left t.isLt]
      rfl
    | succ a =>
      have hlen : (List.ofFn c).length ≤ (a+1)*(L+1)+t.val := by
        rw [List.length_ofFn,Nat.succ_mul]
        omega
      have hsub : (a+1)*(L+1)+t.val - (List.ofFn c).length = a*(L+1)+t.val := by
        rw [List.length_ofFn,Nat.succ_mul]
        omega
      rw [List.getElem?_append_right hlen,hsub,ih]
      simp

/-- On concatenated bit blocks, the block-aligned property is LCS over the letters. -/
theorem blockCommon_iff {K : Type*} {L : ℕ} (W : K → List (Fin (L+1) → Bool)) (ℓ : ℕ) :
    BlockCommon (fun i => bits (W i)) L ℓ ↔ CommonSubsequence W ℓ := by
  rw [commonSubsequence_iff_embedding]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z,fun i => ?_⟩
    obtain ⟨a,ha,h⟩ := hz i
    have hget : ∀ j, ∃ hlt : a j < (W i).length, (W i)[a j] = z j := by
      intro j
      have h0 : (bits (W i))[a j*(L+1)+(0 : Fin (L+1)).val]? = some (z j 0) := h j 0
      rw [bits_getElem?] at h0
      obtain ⟨c,hc,_⟩ := Option.map_eq_some_iff.mp h0
      obtain ⟨hlt,_⟩ := List.getElem?_eq_some_iff.mp hc
      refine ⟨hlt,funext fun t => ?_⟩
      have ht : (bits (W i))[a j*(L+1)+t.val]? = some (z j t) := h j t
      rw [bits_getElem?,List.getElem?_eq_getElem hlt] at ht
      exact Option.some.inj ht
    choose hlt hval using hget
    refine ⟨OrderEmbedding.ofStrictMono (fun j => ⟨a j,hlt j⟩) (fun x y hxy => ha hxy),
      fun j => ?_⟩
    exact (hval j).symm
  · rintro ⟨z,hz⟩
    refine ⟨z,fun i => ?_⟩
    obtain ⟨e,he⟩ := hz i
    refine ⟨fun j => (e j).val,fun x y hxy => e.strictMono hxy,fun j t => ?_⟩
    change (bits (W i))[(e j).val*(L+1)+t.val]? = some (z j t)
    rw [bits_getElem?,List.getElem?_eq_getElem (e j).isLt,he j]
    rfl

/-! ## The full reduction -/
section
variable {k L : ℕ}

/-- The rows of the target: every word as its concatenated bit blocks. -/
abbrev bitWords (W : Fin k → List (Fin (L+1) → Bool)) : Fin k → List Bool :=
  fun i => bits (W i)

noncomputable def rawPair (W : Fin k → List (Fin (L+1) → Bool)) (ℓ : ℕ) : GraphPair :=
  ⟨_,_,inferInstance,inferInstance,sourceGraph k (totalLength (bitWords W)) ℓ L,
    targetGraph (bitWords W) L⟩

/-- Only lengths are tested during preprocessing; LCS itself is never decided here. -/
noncomputable def reduce (W : Fin k → List (Fin (L+1) → Bool)) (ℓ : ℕ) : GraphPair :=
  if k = 0 ∨ ℓ = 0 then yesPair
  else if ∃ i, (W i).length < ℓ then noPair
  else rawPair W ℓ

theorem trivial_yes {ℓ : ℕ} (W : Fin k → List (Fin (L+1) → Bool)) (h : k = 0 ∨ ℓ = 0) :
    CommonSubsequence W ℓ := by
  rcases h with h | rfl
  · subst k
    exact ⟨List.replicate ℓ (fun _ => false),by simp,fun i => Fin.elim0 i⟩
  · exact ⟨[],rfl,fun _ => List.nil_sublist _⟩

theorem trivial_no {ℓ : ℕ} (W : Fin k → List (Fin (L+1) → Bool))
    (h : ∃ i, (W i).length < ℓ) : ¬CommonSubsequence W ℓ := by
  obtain ⟨i,hi⟩ := h
  rintro ⟨z,hz,hs⟩
  have hh := (hs i).length_le
  omega

/-- Correctness for every LCS instance over the alphabet of `L+1`-bit letters. -/
theorem reduce_correct (W : Fin k → List (Fin (L+1) → Bool)) (ℓ : ℕ) :
    (reduce W ℓ).Accepts ↔ CommonSubsequence W ℓ := by
  classical
  unfold reduce
  split_ifs with hyes hno
  · exact ⟨fun _ => trivial_yes W hyes,fun _ => yesPair_accepts⟩
  · exact ⟨fun h => False.elim (noPair_rejects h),fun h => False.elim (trivial_no W hno h)⟩
  · exact (block_graph_iff (bitWords W) (word_le_total (bitWords W))).trans (blockCommon_iff W ℓ)

theorem reduce_width (W : Fin k → List (Fin (L+1) → Bool)) (ℓ : ℕ) :
    (reduce W ℓ).WidthBound k := by
  classical
  unfold reduce
  split_ifs
  · exact (trivial_width k).1
  · exact (trivial_width k).2
  · exact ⟨source_width k _ ℓ L,final_target_width (bitWords W) L⟩

/-- Polynomial output size in the bit length of the words alone. -/
theorem reduce_size (W : Fin k → List (Fin (L+1) → Bool)) (ℓ : ℕ) :
    (reduce W ℓ).SizeBound (dataSize (bitWords W)) := by
  classical
  unfold reduce
  split_ifs with hyes hno
  · exact (trivial_size _).1
  · exact (trivial_size _).2
  · have hk : 0 < k := by omega
    have hℓ : 0 < ℓ := by omega
    have h1 : ℓ ≤ (W ⟨0,hk⟩).length := by
      by_contra h
      exact hno ⟨⟨0,hk⟩,by omega⟩
    have h2 := word_le_total (bitWords W) ⟨0,hk⟩
    have h3 : ℓ*(L+1) ≤ totalLength (bitWords W) := by
      refine le_trans ?_ h2
      change ℓ*(L+1) ≤ (bits (W ⟨0,hk⟩)).length
      rw [bits_length]
      exact Nat.mul_le_mul_right _ h1
    have h4 : ℓ ≤ ℓ*(L+1) := Nat.le_mul_of_pos_right _ (by omega)
    have h5 : L+1 ≤ ℓ*(L+1) := Nat.le_mul_of_pos_left _ hℓ
    have hs : totalLength (bitWords W) ≤ dataSize (bitWords W) := by
      dsimp [dataSize,totalLength]
      omega
    have hks : k ≤ dataSize (bitWords W) := by
      dsimp [dataSize]
      omega
    exact ⟨LCSInstance.graph_bound_of_domain _
        (query_domain_bound hks hs (by omega) (by omega) (by omega)),
      LCSInstance.graph_bound_of_domain _ (LCSInstance.target_domain_bound (bitWords W))⟩

/-- The full combinatorial reduction for letters of `L+1` bits: decision
equivalence, parameter bound, target width three and polynomial size. -/
theorem full_reduction (W : Fin k → List (Fin (L+1) → Bool)) (ℓ : ℕ) :
    ((reduce W ℓ).Accepts ↔ CommonSubsequence W ℓ) ∧
    (reduce W ℓ).WidthBound k ∧ (reduce W ℓ).SizeBound (dataSize (bitWords W)) :=
  ⟨reduce_correct W ℓ,reduce_width W ℓ,reduce_size W ℓ⟩

end

/-! ## Arbitrary finite alphabets -/

/-- Injective relabelling of letters does not change the LCS decision problem. -/
theorem commonSubsequence_map {K α β : Type*} [Nonempty α] (code : α → β)
    (hc : Function.Injective code) (words : K → List α) (ℓ : ℕ) :
    CommonSubsequence (fun i => (words i).map code) ℓ ↔ CommonSubsequence words ℓ := by
  constructor
  · rintro ⟨z,hz,hs⟩
    rcases isEmpty_or_nonempty K with hK | ⟨⟨i0⟩⟩
    · exact ⟨List.replicate ℓ (Classical.arbitrary α),by simp,fun i => isEmptyElim i⟩
    · have pre : ∀ i, ∃ y : List α, y.Sublist (words i) ∧ z = y.map code :=
        fun i => List.sublist_map_iff.mp (hs i)
      choose y hy hzy using pre
      refine ⟨y i0,?_,fun i => ?_⟩
      · rw [← hz,hzy i0,List.length_map]
      · have he : y i = y i0 :=
          (List.map_injective_iff.mpr hc) ((hzy i).symm.trans (hzy i0))
        rw [← he]
        exact hy i
  · rintro ⟨z,hz,hs⟩
    exact ⟨z.map code,by simp [hz],fun i => (hs i).map code⟩

/-- Every finite alphabet has an injective binary code of logarithmic length. -/
theorem exists_code (α : Type*) [Fintype α] :
    ∃ code : α → Fin (Nat.clog 2 (Fintype.card α)+1) → Bool, Function.Injective code := by
  have h1 : Fintype.card α ≤ 2^Nat.clog 2 (Fintype.card α) := Nat.le_pow_clog (by omega) _
  have h2 : 2^Nat.clog 2 (Fintype.card α) ≤ 2^(Nat.clog 2 (Fintype.card α)+1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : Fintype.card α ≤ Fintype.card (Fin (Nat.clog 2 (Fintype.card α)+1) → Bool) := by
    simpa using h1.trans h2
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h3
  exact ⟨e,e.injective⟩

/-- The reduction for words over any alphabet with an injective `L+1`-bit code. -/
theorem alphabet_reduction {k L : ℕ} {α : Type*} [Nonempty α] (code : α → Fin (L+1) → Bool)
    (hc : Function.Injective code) (words : Fin k → List α) (ℓ : ℕ) :
    let P := reduce (fun i => (words i).map code) ℓ
    (P.Accepts ↔ CommonSubsequence words ℓ) ∧ P.WidthBound k ∧
      P.SizeBound (k+(L+1)*(∑ i, (words i).length)+1) := by
  have h := full_reduction (fun i => (words i).map code) ℓ
  have hsize : dataSize (bitWords (fun i => (words i).map code)) =
      k+(L+1)*(∑ i, (words i).length)+1 := by
    simp only [dataSize,bitWords,bits_length,List.length_map,Finset.mul_sum]
    congr 2
    exact Finset.sum_congr rfl (fun i _ => Nat.mul_comm _ _)
  refine ⟨h.1.trans (commonSubsequence_map code hc words ℓ),h.2.1,?_⟩
  rw [← hsize]
  exact h.2.2

/-- LCS over any nonempty finite alphabet reduces to graph homomorphism with
source width at most `max(2k,3)`, target width at most three, and size
polynomial in `k`, the total word length and the logarithm of the alphabet size. -/
theorem alphabet_full_reduction {k : ℕ} {α : Type*} [Fintype α] [Nonempty α]
    (words : Fin k → List α) (ℓ : ℕ) :
    ∃ P : GraphPair, (P.Accepts ↔ CommonSubsequence words ℓ) ∧ P.WidthBound k ∧
      P.SizeBound (k+(Nat.clog 2 (Fintype.card α)+1)*(∑ i, (words i).length)+1) := by
  obtain ⟨code,hc⟩ := exists_code α
  exact ⟨_,alphabet_reduction code hc words ℓ⟩

end TreewidthHom.BlockLCS
