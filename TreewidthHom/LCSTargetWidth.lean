module

public import TreewidthHom.LCSQueryWidth
public import TreewidthHom.ChainGraft
public import TreewidthHom.GraftDecomposition

@[expose] public section

namespace TreewidthHom.LCSInstance
open SimpleGraph
variable {k : ℕ} (words : Fin k → List Bool)

abbrev TargetBase := Fin (k+1) ⊕ (Σ i, Fin ((words i).length+1))

def baseVertex : TargetBase words → TargetVertex words
  | .inl i => .anchor i
  | .inr ⟨i,p⟩ => .pos i p

def rowGraft : RootedGraft (Fin (k+1)) (Σ i, Fin ((words i).length+1)) :=
  chainGraft Fin.succ (fun i => (words i).length+1)

def fullEquiv : (TargetBase words ⊕ Bool) ≃ TargetVertex words :=
  (Equiv.sumAssoc _ _ _).trans (targetEquiv words).symm

@[simp] theorem fullEquiv_inl (x : TargetBase words) :
    fullEquiv words (.inl x) = baseVertex words x := by
  rcases x with a | ⟨i,p⟩ <;> rfl

theorem row_consecutive (i : Fin k) (a b : Fin ((words i).length+1)) (h : b.val = a.val+1) :
    ((rowGraft words).toGraft.graph (pathGraph (k+1))).Adj (.inr ⟨i,a⟩) (.inr ⟨i,b⟩) := by
  right
  have hb : b.val ≠ 0 := by omega
  change (if h : b.val = 0 then _ else _) = _
  rw [dite_eq_right hb]
  congr 1
  apply congrArg (fun j : Fin ((words i).length+1) => (⟨i,j⟩ : Σ i, Fin ((words i).length+1)))
  apply Fin.ext
  dsimp only
  omega

theorem target_edge_base {r : Fin 5} {x y : TargetBase words}
    (hne : x ≠ y) (h : TargetEdge words r (baseVertex words x) (baseVertex words y)) :
    ((rowGraft words).toGraft.graph (pathGraph (k+1))).Adj x y := by
  rcases x with a | ⟨i,p⟩ <;> rcases y with b | ⟨j,q⟩
  · cases h with
    | next i => exact pathGraph_adj.mpr (Or.inl rfl)
  · cases h with
    | begin i => rfl
  · cases h
  · cases h with
    | step i a b hs =>
      rcases hs with he | he
      · have hab : p = b := Fin.ext he.symm
        exact False.elim (hne (by simp [hab]))
      · exact row_consecutive words i p b he
    | advance i a b he => exact row_consecutive words i p b he

/-- The width-three certificate of the written proof: without the letter vertices
the Gaifman graph is a tree, decomposed with two-element bags; both letters are
then added to every bag. -/
theorem target_width :
    ∃ B : Type, ∃ T : SimpleGraph B, ∃ D : Decomposition (target words).gaifman T,
      ∀ b, (D.bag b).card ≤ 4 := by
  classical
  let D0 := pathDecomposition k
  choose owner ho using D0.vertex_cover
  let F := (rowGraft words).toGraft
  let D1 := F.forestDecomposition D0 owner ho
  have hw : ∀ b, (D1.bag b).card ≤ 1+1 := by
    intro b
    exact F.forest_width D0 owner ho (k := 1) (pathDecomposition_width k) b
  let H := (target words).gaifman.comap (fullEquiv words)
  have hbase : ∀ {x y : TargetBase words}, H.Adj (.inl x) (.inl y) →
      (F.graph (pathGraph (k+1))).Adj x y := by
    intro x y h
    change (target words).gaifman.Adj (fullEquiv words (.inl x)) (fullEquiv words (.inl y)) at h
    rw [fullEquiv_inl,fullEquiv_inl] at h
    rcases h with ⟨hne,r,h | h⟩
    · exact target_edge_base words (fun he => hne (congrArg (baseVertex words) he)) h
    · exact (F.graph (pathGraph (k+1))).adj_symm
        (target_edge_base words (fun he => hne (congrArg (baseVertex words) he.symm)) h)
  let D2 := D1.addApices H hbase
  have hedge : ∀ u v, (target words).gaifman.Adj (fullEquiv words u) (fullEquiv words v) → H.Adj u v :=
    fun _ _ h => h
  let D3 := D2.mapEquiv (fullEquiv words) hedge
  refine ⟨_,_,D3,?_⟩
  intro b
  change ((D2.mapEquiv (fullEquiv words) hedge).bag b).card ≤ 4
  rw [Decomposition.mapEquiv_card]
  exact D1.two_apex_width hw (by decide : Fintype.card Bool ≤ 2) b

end TreewidthHom.LCSInstance
