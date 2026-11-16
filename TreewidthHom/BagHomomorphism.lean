module

public import TreewidthHom.TreeDecomposition

@[expose] public section

/-!
# Local assignments on decomposition bags characterize homomorphisms

For a supplied path decomposition, this is the correctness argument for the
XNLP membership algorithm: guess one bag assignment at a time and check local
edges and agreement on the overlap with the preceding bag. The gluing lemma
works for any tree decomposition. It does not assert machine resource bounds.
-/
namespace TreewidthHom
open SimpleGraph

namespace Decomposition

variable {V B W : Type*} [DecidableEq V]
variable {G : SimpleGraph V} {T : SimpleGraph B}

/-- Only images of vertices in the current bag are stored. -/
abbrev BagAssignment (D : Decomposition G T) (W : Type*) :=
  (b : B) → {v : V // v ∈ D.bag b} → W

/-- Consecutive bags agree on their common vertices. -/
def Compatible (D : Decomposition G T) (σ : D.BagAssignment W) : Prop :=
  ∀ a b, T.Adj a b → ∀ v (ha : v ∈ D.bag a) (hb : v ∈ D.bag b),
    σ a ⟨v,ha⟩ = σ b ⟨v,hb⟩

/-- Every source edge whose endpoints are in one bag is preserved. -/
def PreservesBagEdges (D : Decomposition G T) (H : SimpleGraph W)
    (σ : D.BagAssignment W) : Prop :=
  ∀ b u v (hu : u ∈ D.bag b) (hv : v ∈ D.bag b), G.Adj u v →
    H.Adj (σ b ⟨u,hu⟩) (σ b ⟨v,hv⟩)

theorem agree_on_walk (D : Decomposition G T) (σ : D.BagAssignment W)
    (hc : D.Compatible σ) {a b : B} (p : T.Walk a b) (v : V)
    (hp : ∀ c ∈ p.support, v ∈ D.bag c)
    (ha : v ∈ D.bag a) (hb : v ∈ D.bag b) :
    σ a ⟨v,ha⟩ = σ b ⟨v,hb⟩ := by
  induction p with
  | nil => rfl
  | @cons a c b hac p ih =>
    have htail : ∀ d ∈ p.support, v ∈ D.bag d := by
      intro d hd
      exact hp d (by simp only [Walk.support_cons, List.mem_cons]; exact Or.inr hd)
    have hvc : v ∈ D.bag c := htail c p.start_mem_support
    exact (hc a c hac v ha hvc).trans (ih htail hvc hb)

theorem agree_on_bags (D : Decomposition G T) (σ : D.BagAssignment W)
    (hc : D.Compatible σ) (v : V) (a b : B)
    (ha : v ∈ D.bag a) (hb : v ∈ D.bag b) :
    σ a ⟨v,ha⟩ = σ b ⟨v,hb⟩ := by
  obtain ⟨p,hp⟩ := D.running v a b ha hb
  exact D.agree_on_walk σ hc p v hp ha hb

/-- Local edge checks and overlap checks are sufficient and necessary. -/
theorem hom_iff_bagAssignments (D : Decomposition G T) (H : SimpleGraph W) :
    Nonempty (G →g H) ↔
      ∃ σ : D.BagAssignment W, D.Compatible σ ∧ D.PreservesBagEdges H σ := by
  classical
  constructor
  · rintro ⟨f⟩
    refine ⟨fun _ v => f v.val, ?_, ?_⟩
    · intro a b hab v ha hb
      rfl
    · intro b u v hu hv huv
      exact f.map_rel huv
  · rintro ⟨σ,hc,he⟩
    choose atBag memBag using D.vertex_cover
    let f : V → W := fun v => σ (atBag v) ⟨v,memBag v⟩
    have hf : ∀ b v (hv : v ∈ D.bag b), f v = σ b ⟨v,hv⟩ := by
      intro b v hv
      exact D.agree_on_bags σ hc v (atBag v) b (memBag v) hv
    refine ⟨⟨f, ?_⟩⟩
    intro u v huv
    obtain ⟨b,hu,hv⟩ := D.edge_cover huv
    rw [hf b u hu, hf b v hv]
    exact he b u v hu hv huv

/-- On a path, only the overlap with the immediately preceding bag is checked. -/
theorem compatible_path_iff {n : ℕ} (D : Decomposition G (pathGraph (n+1)))
    (σ : D.BagAssignment W) :
    D.Compatible σ ↔
      ∀ (a b : Fin (n+1)), a.val+1 = b.val →
        ∀ (v : V) (ha : v ∈ D.bag a) (hb : v ∈ D.bag b),
          σ a ⟨v,ha⟩ = σ b ⟨v,hb⟩ := by
  constructor
  · intro hc a b hab v ha hb
    exact hc a b (pathGraph_adj.mpr (Or.inl hab)) v ha hb
  · intro hs a b hab v ha hb
    rcases pathGraph_adj.mp hab with hab | hba
    · exact hs a b hab v ha hb
    · exact (hs b a hba v hb ha).symm

/-- The exact acceptance condition of the successive-bag membership algorithm. -/
theorem hom_iff_pathBagAssignments {n : ℕ} (D : Decomposition G (pathGraph (n+1)))
    (H : SimpleGraph W) :
    Nonempty (G →g H) ↔
      ∃ σ : D.BagAssignment W, D.PreservesBagEdges H σ ∧
        ∀ (a b : Fin (n+1)), a.val+1 = b.val →
          ∀ (v : V) (ha : v ∈ D.bag a) (hb : v ∈ D.bag b),
            σ a ⟨v,ha⟩ = σ b ⟨v,hb⟩ := by
  simp only [D.hom_iff_bagAssignments H, D.compatible_path_iff, and_comm]

/-- A width-w bag has at most w+1 vertex-image records. -/
theorem bag_domain_card (D : Decomposition G T) (b : B) :
    Fintype.card {v : V // v ∈ D.bag b} = (D.bag b).card := by
  simp

/-- Keeping two consecutive bags uses at most 2(w+1) vertex-image records. -/
theorem two_bag_records_le (D : Decomposition G T) (w : ℕ)
    (hw : ∀ b, (D.bag b).card ≤ w+1) (a b : B) :
    Fintype.card {v : V // v ∈ D.bag a} +
      Fintype.card {v : V // v ∈ D.bag b} ≤ 2*(w+1) := by
  rw [D.bag_domain_card a, D.bag_domain_card b]
  have := hw a
  have := hw b
  omega

end Decomposition
end TreewidthHom
