module

public import Mathlib

@[expose] public section

/-!
# Tree-decomposition certificates and apex extension

The pinned mathlib release supplies trees and walks. We define a decomposition
certificate directly from those notions: vertex coverage, edge coverage, and
connected occurrence bags. Width bounds are maximum bag cardinality minus one.
-/
namespace TreewidthHom

open SimpleGraph

/-- A tree decomposition over a specified tree of bags. -/
structure Decomposition {V B : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : SimpleGraph B) where
  tree : T.IsTree
  bag : B → Finset V
  vertex_cover : ∀ v, ∃ b, v ∈ bag b
  edge_cover : ∀ {u v}, G.Adj u v → ∃ b, u ∈ bag b ∧ v ∈ bag b
  running : ∀ v a b, v ∈ bag a → v ∈ bag b →
    ∃ p : T.Walk a b, ∀ c ∈ p.support, v ∈ bag c

namespace Decomposition

variable {V B A : Type*} [DecidableEq V] [DecidableEq A] [Fintype A]
variable {G : SimpleGraph V} {T : SimpleGraph B}

/-- Add all apex vertices to every bag, keeping the same decomposition tree. -/
def apexBag (D : Decomposition G T) (b : B) : Finset (V ⊕ A) :=
  (D.bag b).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

@[simp] theorem inl_mem_apexBag (D : Decomposition G T) (b : B) (v : V) :
    Sum.inl v ∈ D.apexBag (A := A) b ↔ v ∈ D.bag b := by
  simp [apexBag]

@[simp] theorem inr_mem_apexBag (D : Decomposition G T) (b : B) (v : A) :
    Sum.inr v ∈ D.apexBag (A := A) b := by
  simp [apexBag]

/-- Arbitrary apex edges can be covered by adding the apices to every bag. -/
noncomputable def addApices (D : Decomposition G T) (H : SimpleGraph (V ⊕ A))
    (hbase : ∀ {u v}, H.Adj (Sum.inl u) (Sum.inl v) → G.Adj u v) :
    Decomposition H T where
  tree := D.tree
  bag := D.apexBag
  vertex_cover := by
    rintro (v | a)
    · obtain ⟨b, hb⟩ := D.vertex_cover v
      exact ⟨b, (D.inl_mem_apexBag b v).mpr hb⟩
    · let := D.tree.connected.nonempty
      exact ⟨Classical.arbitrary B, D.inr_mem_apexBag _ a⟩
  edge_cover := by
    rintro (u | u) (v | v) h
    · obtain ⟨b, hu, hv⟩ := D.edge_cover (hbase h)
      exact ⟨b, (D.inl_mem_apexBag b u).mpr hu, (D.inl_mem_apexBag b v).mpr hv⟩
    · obtain ⟨b, hu⟩ := D.vertex_cover u
      exact ⟨b, (D.inl_mem_apexBag b u).mpr hu, D.inr_mem_apexBag b v⟩
    · obtain ⟨b, hv⟩ := D.vertex_cover v
      exact ⟨b, D.inr_mem_apexBag b u, (D.inl_mem_apexBag b v).mpr hv⟩
    · let := D.tree.connected.nonempty
      exact ⟨Classical.arbitrary B, D.inr_mem_apexBag _ u, D.inr_mem_apexBag _ v⟩
  running := by
    rintro (v | v) a b ha hb
    · obtain ⟨p, hp⟩ := D.running v a b
        ((D.inl_mem_apexBag a v).mp ha) ((D.inl_mem_apexBag b v).mp hb)
      exact ⟨p, fun c hc => (D.inl_mem_apexBag c v).mpr (hp c hc)⟩
    · obtain ⟨p⟩ := D.tree.connected a b
      exact ⟨p, fun c _ => D.inr_mem_apexBag c v⟩

theorem apexBag_card (D : Decomposition G T) (b : B) :
    (D.apexBag (A := A) b).card ≤ (D.bag b).card + Fintype.card A := by
  calc
    _ ≤ ((D.bag b).map ⟨Sum.inl, Sum.inl_injective⟩).card +
      (Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩ : Finset (V ⊕ A)).card := Finset.card_union_le _ _
    _ = _ := by simp

/-- The target-width argument's generic step: two apices raise width by at most two. -/
theorem two_apex_width (D : Decomposition G T) {k : ℕ}
    (hwidth : ∀ b, (D.bag b).card ≤ k + 1) (hA : Fintype.card A ≤ 2) :
    ∀ b, (D.apexBag (A := A) b).card ≤ (k + 2) + 1 := by
  intro b
  have h := D.apexBag_card (A := A) b
  have hw := hwidth b
  omega

end Decomposition
end TreewidthHom
