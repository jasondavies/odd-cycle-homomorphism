module

public import TreewidthHom.ChainGraft
public import TreewidthHom.ColorEncoding
public import TreewidthHom.DirectionWidth

@[expose] public section

namespace TreewidthHom.TypedDag
variable {C : Type} {V B : Type*} (A : TypedDag C V) (M : Markers C)

abbrev CyclePrivate := Σ v : V, Fin (M.length (A.color v)-1)

def cycleSplit (z : A.Decorated M) : V ⊕ A.CyclePrivate M :=
  if h : z.2.val = 0 then .inl z.1
  else .inr ⟨z.1,⟨z.2.val-1,by have := z.2.val_lt; omega⟩⟩

def cycleJoin : V ⊕ A.CyclePrivate M → A.Decorated M
  | .inl v => ⟨v,0⟩
  | .inr ⟨v,j⟩ => ⟨v,((j.val+1 : ℕ) : ZMod (M.length (A.color v)))⟩

def cycleEquiv : A.Decorated M ≃ (V ⊕ A.CyclePrivate M) where
  toFun := A.cycleSplit M
  invFun := A.cycleJoin M
  left_inv := by
    rintro ⟨v,z⟩
    by_cases hz : z.val = 0
    · have hzero : z = 0 := (ZMod.val_eq_zero z).mp hz
      simp [cycleSplit,cycleJoin,hzero]
    · simp only [cycleSplit,dite_eq_right hz,cycleJoin]
      have he : z.val-1+1 = z.val := by omega
      simp [he]
  right_inv := by
    rintro (v | ⟨v,j⟩)
    · simp [cycleSplit,cycleJoin]
    · have hj : j.val+1 < M.length (A.color v) := by have := j.isLt; omega
      have hz := ZMod.val_cast_of_lt hj
      dsimp only [cycleSplit,cycleJoin]
      simp only [hz,Nat.add_sub_cancel]
      simp

def base : Digraph V where
  edge := A.edge
  loopless := fun _ h => (Nat.lt_irrefl _) (A.increases h)

def cycleGraft : RootedGraft V (A.CyclePrivate M) :=
  chainGraft id (fun v => M.length (A.color v)-1)

theorem cycle_edge_in_cone (v : V) (z : ZMod (M.length (A.color v))) :
    ((A.cycleGraft M).cone A.base.underlying).Adj
      (A.cycleSplit M ⟨v,z⟩) (A.cycleSplit M ⟨v,z+1⟩) := by
  have hp := (M.prime (A.color v)).two_le
  have hlt := z.val_lt
  have hs : (z+1).val = (z.val+1) % M.length (A.color v) := by
    rw [ZMod.val_add,ZMod.val_one]
  by_cases hz : z.val = 0
  · have hn : (z+1).val = 1 := by rw [hs,hz]; simp [Nat.mod_eq_of_lt (by omega : 1 < M.length (A.color v))]
    simp [cycleSplit,hz,hn,cycleGraft,RootedGraft.cone,chainGraft]
  · by_cases hn : (z+1).val = 0
    · simp [cycleSplit,hz,hn,cycleGraft,RootedGraft.cone,chainGraft]
    · have hsmall : z.val+1 < M.length (A.color v) := by
        by_contra h
        have he : z.val+1 = M.length (A.color v) := by omega
        rw [he,Nat.mod_self] at hs
        exact hn hs
      rw [Nat.mod_eq_of_lt hsmall] at hs
      simp [cycleSplit,hz,cycleGraft,RootedGraft.cone,chainGraft,hs]

theorem encoded_edge_in_cone {x y : A.Decorated M} (h : A.EncodedEdge M x y) :
    ((A.cycleGraft M).cone A.base.underlying).Adj (A.cycleSplit M x) (A.cycleSplit M y) := by
  cases h with
  | cycle v z => exact A.cycle_edge_in_cone M v z
  | base h =>
    simp only [cycleSplit,ZMod.val_zero]
    exact Or.inl h

/-- A fan of bags of size three covers each marker cycle, independently of its length. -/
theorem colorEncoding_width [DecidableEq V] {T : SimpleGraph B}
    (D : Decomposition A.base.underlying T) {k : ℕ}
    (hw : ∀ b, (D.bag b).card ≤ k+1) :
    ∃ T' : SimpleGraph (B ⊕ A.CyclePrivate M),
      ∃ D' : Decomposition (A.encoded M).underlying T',
        ∀ b, (D'.bag b).card ≤ max k 2+1 := by
  classical
  choose owner ho using D.vertex_cover
  let F := A.cycleGraft M
  let D0 := F.decomposition D owner ho
  have he : ∀ u v, (A.encoded M).underlying.Adj ((A.cycleEquiv M).symm u) ((A.cycleEquiv M).symm v) →
      (F.cone A.base.underlying).Adj u v := by
    intro u v h
    change A.EncodedEdge M _ _ ∨ A.EncodedEdge M _ _ at h
    rcases h with h | h
    · simpa only [← show (A.cycleEquiv M).toFun = A.cycleSplit M from rfl,
        Equiv.toFun_as_coe,Equiv.apply_symm_apply] using A.encoded_edge_in_cone M h
    · have hh := (F.cone A.base.underlying).adj_symm (A.encoded_edge_in_cone M h)
      simpa only [← show (A.cycleEquiv M).toFun = A.cycleSplit M from rfl,
        Equiv.toFun_as_coe,Equiv.apply_symm_apply] using hh
  refine ⟨(F.indexGraft owner).graph T,D0.mapEquiv (A.cycleEquiv M).symm he,?_⟩
  intro b
  rw [Decomposition.mapEquiv_card]
  exact F.width D hw b

end TreewidthHom.TypedDag
