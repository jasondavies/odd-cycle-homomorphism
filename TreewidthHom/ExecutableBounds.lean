module
public import TreewidthHom.EdgeList
@[expose] public section
namespace TreewidthHom.Executable
theorem untyped_width {V : Type} (A : UnaryBinary V) {w : ℕ}
    (h : HasWidth A.gaifman w) :
    HasWidth (A.asRelational.untypedGraph markers) (max w 12) := by
  classical
  obtain ⟨d,B,T,D,hw⟩ := h
  let := d
  have ha : ∀ r, Relational.schemaArity r ≤ 2 := by
    intro r; unfold Relational.schemaArity; split <;> omega
  obtain ⟨T1,D1,h1⟩ := A.asRelational.incidence_width D ha (A.fact_bag D) hw
  obtain ⟨T2,D2,h2⟩ := A.asRelational.typedDag.colorEncoding_width markers D1 h1
  obtain ⟨T3,D3,h3⟩ := (A.asRelational.typedDag.encoded markers).directionReduction_width D2 h2
  refine ⟨_,_,T3,D3,?_⟩
  intro b
  have hb := h3 b
  omega

theorem graph_card_le {V : Type*} [Fintype V]
    (A : Relational (Fin 6) Relational.schemaArity V) :
    Fintype.card (Arrow.AssemblyVertex (A.typedDag.Decorated markers)
      (A.typedDag.encoded markers).Arc) ≤ 20000000 * (Fintype.card V + 1)^4 := by
  have ha : ∀ r : Fin 6, Relational.schemaArity r ≤ 2 := by
    intro r; unfold Relational.schemaArity; split <;> omega
  have hf := A.fact_card_le ha
  have hv := A.vertex_card_le ha
  simp only [Fintype.card_fin] at hf
  have hd := decorated_card_le A.typedDag markers
    markers_bound
  let n := Fintype.card V
  let d := Fintype.card (A.typedDag.Decorated markers)
  have hdb : d ≤ 1273 * (n+1)^2 := by
    dsimp [d,n]
    nlinarith [sq_nonneg (Fintype.card V : ℤ)]
  have harc : Fintype.card (A.typedDag.encoded markers).Arc ≤ d^2 := by
    calc
      _ ≤ Fintype.card (A.typedDag.Decorated markers × A.typedDag.Decorated markers) :=
        Fintype.card_subtype_le _
      _ = d^2 := by simp [d,pow_two]
  rw [Digraph.directionReduction_card]
  change d + 11 * Fintype.card (A.typedDag.encoded markers).Arc ≤ 20000000 * (n+1)^4
  have hsq : d^2 ≤ (1273 * (n+1)^2)^2 := Nat.pow_le_pow_left hdb 2
  have hn : (n+1)^2 ≤ (n+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

theorem domain_size_bound {V : Type} [Fintype V]
    (A : Relational (Fin 6) Relational.schemaArity V) {s : ℕ}
    (h : Fintype.card V+1 ≤ 8*(s+1)^3) :
    Fintype.card (Arrow.AssemblyVertex (A.typedDag.Decorated markers)
      (A.typedDag.encoded markers).Arc) ≤ 1000000000000*(s+1)^12 := by
  have h1 := graph_card_le A
  have h2 := Nat.pow_le_pow_left h 4
  have he : (8*(s+1)^3)^4 = 4096*(s+1)^12 := by ring
  rw [he] at h2
  omega
end TreewidthHom.Executable
