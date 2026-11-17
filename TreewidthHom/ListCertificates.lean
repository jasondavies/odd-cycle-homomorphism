module

public import TreewidthHom.FiniteDecomposition

@[expose] public section

/-!
# Size of supplied decomposition certificates

The reduction's output tree has one index for each input bag, private reference
vertex and internal link vertex. The resulting polynomial is in the numeric
parameters and the supplied bag count; colour-label compaction and bit-level
encodings are separate obligations.
-/

namespace TreewidthHom.OddCycle.ListReduction
open SimpleGraph Reference
variable {m n : ℕ} [Fact (1 < n)]

set_option synthInstance.maxSize 256 in
/-- A finite input tree certificate gives a finitely labelled output certificate
with polynomially many bags and the same additive width bound. -/
theorem source_tree_certificate {N w : ℕ} [DecidableEq (Fin m)]
    (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    {T : SimpleGraph (Fin N)} (D : Decomposition F T)
    (hD : ∀ b, (D.bag b).card ≤ w+1) :
    ∃ d : DecidableEq (SourceVertex F L), ∃ M : ℕ,
      ∃ T' : SimpleGraph (Fin M), ∃ D' : @Decomposition _ _ d (source F L) T',
        (∀ b, (D'.bag b).card ≤ max (w+2) 3+1) ∧
          M ≤ N+m*n*n+(m*n+m*m)*n := by
  classical
  let : Fintype (Link F L) := Subtype.fintype _
  obtain ⟨T', D', hD'⟩ := source_decomposition F L D hD
  let B := (Fin N ⊕ Private m n) ⊕ (Link F L × Fin (n-3))
  let e := (Fintype.equivFin B).symm
  refine ⟨_, Fintype.card B, _, D'.reindex e, (fun b => hD' (e b)), ?_⟩
  have hL : Fintype.card (Link F L) ≤ m*n+m*m := by
    simpa [Code, Copies, ZMod.card] using Fintype.card_subtype_le (Valid F L)
  have hcard : Fintype.card B = N+m*n*(n-2)+Fintype.card (Link F L)*(n-3) := by
    simp [B, Private, Copies, ZMod.card]
  have h1 := Nat.mul_le_mul_left (m*n) (Nat.sub_le n 2)
  have h2 := Nat.mul_le_mul hL (Nat.sub_le n 3)
  rw [hcard]
  omega

/-- Transfer a supplied finite tree certificate with its bag-count bound. -/
theorem source_tree_bag_bound (F : SimpleGraph (Fin m))
    (L : Fin m → Finset (ZMod n)) {w N : ℕ} (h : HasWidthWithBags F w N) :
    HasWidthWithBags (source F L) (max (w+2) 3) (N+m*n*n+(m*n+m*m)*n) := by
  obtain ⟨d, K, T, D, hD, hK⟩ := h
  let := d
  obtain ⟨d', M, T', D', hD', hM⟩ := source_tree_certificate F L D hD
  exact ⟨d', M, T', D', hD', by omega⟩

/-- The serial reference and link sweeps also have a polynomial bag bound. -/
theorem source_path_certificate (F : SimpleGraph (Fin m))
    (L : Fin m → Finset (ZMod n)) (hn : 5 ≤ n) {w N : ℕ}
    (h : HasPathWidthWithBags F w N) :
    HasPathWidthWithBags (source F L) (w+6)
      (N*(2*(m*n*n+2))*((m*n+m*m+1)*n)) := by
  classical
  let : Fintype (Link F L) := Subtype.fintype _
  have hout := pathWidth_linked_of_bags_bound (base m n) (base_le_aug F)
    (fun l : Link F L => src l.val) (fun l => dst l.val) (n-3) (by omega)
    (aug_pathWidth_bag_bound F h) (link_adj_aug F L)
  obtain ⟨d, r, D, hD, hr⟩ := hout
  refine ⟨d, r, D, hD, hr.trans ?_⟩
  have hL : Fintype.card (Link F L) ≤ m*n+m*m := by
    simpa [Code, Copies, ZMod.card] using Fintype.card_subtype_le (Valid F L)
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul_left N (Nat.mul_le_mul_left 2
      (Nat.add_le_add_right (Nat.mul_le_mul_left (m*n) (Nat.sub_le n 2)) 2))
  · exact Nat.mul_le_mul (Nat.add_le_add_right hL 1) (by omega)

end TreewidthHom.OddCycle.ListReduction
