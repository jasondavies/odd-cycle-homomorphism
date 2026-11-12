module
public import TreewidthHom.MeasuredLCS
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace TreewidthHom.Executable
open LCSInstance
namespace EnumRun

def queryVertices (k N ℓ : ℕ) : EnumRun (Executable.queryVertices k N ℓ) :=
  ((fin (k+1)).sum (((fin k).prod (((fin ℓ).prod (fin (N+1))).sum unit)).sum (fin ℓ))).map
    (queryEquiv k N ℓ).symm

/-- Charge a supplied bound for the word lookup and length primitive before
constructing that word's finite position range. -/
def targetVertices {k : ℕ} (words : Fin k → List Bool) (q : ℕ) :
    EnumRun (Executable.targetVertices words) :=
  ((fin (k+1)).sum ((sigma (fin k) (fun i =>
    { run := let a := (fin ((words i).length+1)).run
             ⟨a.value,a.cost+q⟩
      correct := (fin ((words i).length+1)).correct })).sum bool)).map
    (targetEquiv words).symm

theorem queryVertices_level {k N ℓ s : ℕ} (hk : k ≤ s) (hN : N ≤ s) (hℓ : ℓ ≤ s)
    (hs : 100 ≤ s) : (queryVertices k N ℓ).Level 9 s := by
  apply level_map
  apply level_sum
  · exact (level_fin (by omega)).lift (by omega)
  · apply level_sum
    · apply level_prod
      · exact (level_fin (by omega)).lift (by omega)
      · apply level_sum
        · exact level_prod (level_fin (by omega)) (level_fin (by omega))
        · exact (level_unit (by omega)).lift (by omega)
    · exact (level_fin (by omega)).lift (by omega)

theorem targetVertices_level {k q s : ℕ} (words : Fin k → List Bool) (hk : k ≤ s)
    (hN : ∀ i, (words i).length ≤ s) (hq : q ≤ s+1) (hs : 100 ≤ s) :
    (targetVertices words q).Level 6 s := by
  apply level_map
  apply level_sum
  · exact (level_fin (by omega)).lift (by omega)
  · apply level_sum
    · apply level_sigma
      · exact (level_fin (by omega)).lift (by omega)
      · intro i
        have h := level_fin (show (words i).length+1 ≤ s+1 by have := hN i; omega)
        have hq' : q ≤ budget 1 s := hq.trans (budget_mono (show 0 ≤ 1 by omega) s)
        have hlen := h.1
        have hcost := h.2
        constructor
        · exact hlen.trans (budget_step 1 s)
        · change (fin ((words i).length+1)).run.cost+q ≤ grow (budget 1 s)
          unfold grow
          nlinarith [sq_nonneg (budget 1 s : ℤ)]
    · exact (level_bool (by omega)).lift (by omega)

end EnumRun
end TreewidthHom.Executable
