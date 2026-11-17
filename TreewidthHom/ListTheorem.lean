module

public import TreewidthHom.ListPathWidth
public import TreewidthHom.ListFeedback
public import TreewidthHom.CycleWidth

@[expose] public section

namespace TreewidthHom.OddCycle.ListReduction
open SimpleGraph Reference
variable {m n : ℕ} [Fact (1 < n)]

/-- A polynomial bound on the full, explicitly represented source graph. -/
theorem source_card_le (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n)) :
    Nat.card (SourceVertex F L) ≤ 2+m+m*n*n+(m*n+m*m)*n := by
  classical
  let : Fintype (Link F L) := Subtype.fintype _
  have hL := link_card_le F L
  have hV : Nat.card (SourceVertex F L) = 2+m*n*(n-2)+m+Fintype.card (Link F L)*(n-3) := by
    simp [Nat.card_eq_fintype_card,SourceVertex,BaseVertex,RefVertex,Copies,ZMod.card]
  have h1 := Nat.mul_le_mul_left (m*n) (Nat.sub_le n 2)
  have h2 := Nat.mul_le_mul hL (Nat.sub_le n 3)
  rw [hV]
  omega

/-- The complete finite reduction certificate. Complexity classes and machine
resource bounds are deliberately not encoded in this theorem. -/
theorem reduction (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    (hodd : Odd n) (hn : 5 ≤ n) :
    (Nonempty (source F L →g cyc n) ↔ Colorable F L) ∧
    (∀ w, HasWidth F w → HasWidth (source F L) (max (w+2) 3)) ∧
    (∀ w, HasPathWidth F w → HasPathWidth (source F L) (w+6)) ∧
    HasPathWidth (cyc n) 2 ∧
    (∀ S : Finset (Fin m), (F.induce {v | v ∉ S}).IsAcyclic →
      ((source F L).induce {v | ¬ removed S v}).IsAcyclic ∧
      Nat.card {v : SourceVertex F L // removed S v}=S.card+2) ∧
    Nat.card (SourceVertex F L) ≤ 2+m+m*n*n+(m*n+m*m)*n := by
  refine ⟨?_,fun _ hw => source_width F L hw,fun _ hw => source_pathWidth F L hn hw,?_,?_,source_card_le F L⟩
  · exact source_hom_iff_colorable F L hodd hn
  · exact target_pathWidth n (by omega)
  · intro S hS
    exact ⟨source_feedback F L S hn hS,removed_card F L S⟩

end TreewidthHom.OddCycle.ListReduction
