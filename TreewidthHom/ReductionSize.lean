module

public import TreewidthHom.ReductionWidth

@[expose] public section

namespace TreewidthHom.LCSInstance

/-- Includes a delimiter per word, so empty words still contribute to input size.
The requested length is deliberately excluded: preprocessing handles large lengths. -/
def dataSize {k : ℕ} (words : Fin k → List Bool) : ℕ :=
  k + (∑ i, (words i).length) + 1

def totalLength {k : ℕ} (words : Fin k → List Bool) : ℕ := ∑ i, (words i).length

theorem word_le_total {k : ℕ} (words : Fin k → List Bool) (i : Fin k) :
    (words i).length ≤ totalLength words := by
  unfold totalLength
  exact Finset.single_le_sum (f := fun i : Fin k => (words i).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem query_domain_bound {k ℓ : ℕ} (words : Fin k → List Bool)
    (hℓ : ℓ ≤ dataSize words) :
    Fintype.card (QueryVertex k (totalLength words) ℓ) + 1 ≤ 8*(dataSize words+1)^3 := by
  rw [query_card]
  let s := dataSize words
  have hk : k ≤ s := by dsimp [s,dataSize]; omega
  have hN : totalLength words ≤ s := by dsimp [s,dataSize,totalLength]; omega
  have h1 : ℓ*(totalLength words+1) ≤ (s+1)*(s+1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : k*(ℓ*(totalLength words+1)+1) ≤ (s+1)*((s+1)*(s+1)+1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : s+1 ≤ (s+1)^3 := by
    calc
      s+1 = (s+1)^1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  change _ ≤ 8*(s+1)^3
  nlinarith

theorem target_domain_bound {k : ℕ} (words : Fin k → List Bool) :
    Fintype.card (TargetVertex words) + 1 ≤ 8*(dataSize words+1)^3 := by
  rw [target_card]
  have hsum : (∑ i, ((words i).length+1)) = totalLength words+k := by
    simp [totalLength,Finset.sum_add_distrib]
  rw [hsum]
  have h3 : dataSize words+1 ≤ (dataSize words+1)^3 := by
    calc
      dataSize words+1 = (dataSize words+1)^1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  dsimp [dataSize,totalLength] at *
  omega

theorem graph_bound_of_domain {V : Type} [Fintype V]
    (A : Relational (Fin 6) Relational.schemaArity V) {s : ℕ}
    (h : Fintype.card V+1 ≤ 8*(s+1)^3) :
    Fintype.card (Arrow.AssemblyVertex (A.typedDag.Decorated schemaMarkers)
      (A.typedDag.encoded schemaMarkers).Arc) ≤ 1000000000000*(s+1)^12 := by
  have h1 := schema_graph_card_le A
  have h2 := Nat.pow_le_pow_left h 4
  have he : (8*(s+1)^3)^4 = 4096*(s+1)^12 := by ring
  rw [he] at h2
  omega

end TreewidthHom.LCSInstance
