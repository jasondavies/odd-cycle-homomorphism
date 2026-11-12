module

public import TreewidthHom.ArrowGluing
public import TreewidthHom.ArrowQuotient

@[expose] public section

/-! # Confinement in arbitrary gadget assemblies

Collapse all base vertices to one port. A finite, kernel-checked certificate for
maps to this quotient shows that all private images form one connected piece.
Private adjacency preserves the copy index, so the whole map belongs to one
copy; rigidity then fixes every coordinate, including the ordered ports.
-/
namespace TreewidthHom.Arrow.Assembly
variable {V E : Type*} (A : Assembly V E)

/-- Collapse all assembly endpoints; retain private gadget coordinates. -/
def coordinate : AssemblyVertex V E → Fin 13
  | .inl _ => 8
  | .inr (_,v) => v.val

@[simp] theorem coordinate_embed (e : E) (v : Fin 13) :
    coordinate (A.embed e v) = Quotient.collapse v := by
  by_cases h : v = 8 <;> by_cases h' : v = 10 <;>
    simp_all [embed, coordinate, Quotient.collapse]

theorem coordinate_adj {x y : AssemblyVertex V E} (h : A.graph.Adj x y) :
    Quotient.QAdj (coordinate x).val (coordinate y).val := by
  obtain ⟨e,u,v,he,rfl,rfl⟩ := h
  simpa only [coordinate_embed] using Quotient.collapse_adj u v he

theorem private_of_coordinate_ne (x : AssemblyVertex V E)
    (h : (coordinate x).val ≠ 8) : ∃ e w, x = Sum.inr (e,w) := by
  cases x with
  | inl v => exact False.elim (h rfl)
  | inr p => exact ⟨p.1,p.2,rfl⟩

/-- Every homomorphism from the gadget to an arbitrary loopless assembly is the
coordinate-preserving inclusion of one copy. No finite-size bound is assumed. -/
theorem confinement (f : Arrow.graph →g A.graph) :
    ∃ e, ∀ v, f v = A.embed e v := by
  classical
  obtain ⟨d,hd⟩ := Quotient.connectivity_certificate (fun v => coordinate (f v))
    (fun u v h => A.coordinate_adj (f.map_adj h))
  obtain ⟨e,w0,hw0⟩ := private_of_coordinate_ne (f 7) hd.1
  have same_copy : ∀ n, ∀ v, d v = n → (coordinate (f v)).val ≠ 8 →
      ∃ w, f v = Sum.inr (e,w) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn hv
      rcases hd.2.1 v hv with heq | ⟨u,hu,he,hlt⟩
      · subst v
        exact ⟨w0,hw0⟩
      · obtain ⟨w,hw⟩ := ih (d u) (by omega) u rfl hu
        obtain ⟨c,z,hz⟩ := private_of_coordinate_ne (f v) hv
        have hc : c = e := A.private_adj_same_copy (by
          rw [← hz, ← hw]
          exact f.map_adj he)
        subst c
        exact ⟨z,hz⟩
  have image : ∀ v, ∃ u, A.embed e u = f v := by
    intro v
    by_cases hv : (coordinate (f v)).val = 8
    · obtain ⟨u,he,hu⟩ := hd.2.2 v hv
      obtain ⟨w,hw⟩ := same_copy (d u) u rfl hu
      exact A.neighbor_of_private (by
        rw [← hw]
        exact f.map_adj (Arrow.graph.adj_symm he))
    · obtain ⟨w,hw⟩ := same_copy (d v) v rfl hv
      exact ⟨w.val,(A.embed_inner e w).trans hw.symm⟩
  choose g hg using image
  let gh : Arrow.graph →g Arrow.graph :=
    { toFun := g
      map_rel' := by
        intro u v h
        apply (A.embed_adj_iff e (g u) (g v)).mp
        rw [hg u,hg v]
        exact f.map_adj h }
  refine ⟨e,fun v => ?_⟩
  have hfix : g v = v := Arrow.rigid_hom gh v
  simpa only [hfix] using (hg v).symm

end TreewidthHom.Arrow.Assembly
