module

public import Mathlib

@[expose] public section

namespace TreewidthHom
open SimpleGraph

/-- A well-founded family of new parent pointers, ending at an old vertex. -/
structure Graft (B P : Type*) where
  parent : P → B ⊕ P
  height : P → ℕ
  decreases : ∀ p q, parent p = Sum.inr q → height q < height p

namespace Graft
variable {B P : Type*} (F : Graft B P) (T : SimpleGraph B)

def graph : SimpleGraph (B ⊕ P) where
  Adj
    | .inl u, .inl v => T.Adj u v
    | .inl b, .inr p => F.parent p = .inl b
    | .inr p, .inl b => F.parent p = .inl b
    | .inr p, .inr q => F.parent p = .inr q ∨ F.parent q = .inr p
  symm := ⟨by
    rintro (u | u) (v | v) h
    · exact T.adj_symm h
    · exact h
    · exact h
    · exact h.elim Or.inr Or.inl⟩
  loopless := ⟨by
    rintro (b | p) h
    · exact T.loopless.irrefl b h
    · rcases h with h | h <;> exact (Nat.lt_irrefl _) (F.decreases p p h)⟩

def rank : B ⊕ P → ℕ
  | .inl _ => 0
  | .inr p => F.height p + 1

theorem parent_adj (p : P) : (F.graph T).Adj (.inr p) (F.parent p) := by
  cases h : F.parent p with
  | inl b => exact h
  | inr q => exact Or.inl h

def inclusion : T →g F.graph T where
  toFun := Sum.inl
  map_rel' := fun h => h

theorem reaches_base : ∀ p : P, ∃ b, (F.graph T).Reachable (.inr p) (.inl b) := by
  intro p
  induction h : F.height p using Nat.strong_induction_on generalizing p with
  | h n ih =>
    have hedge := (F.parent_adj T p).reachable
    cases hp : F.parent p with
    | inl b => exact ⟨b, by simpa [hp] using hedge⟩
    | inr q =>
      obtain ⟨b, hb⟩ := ih _ (h ▸ F.decreases p q hp) q rfl
      exact ⟨b, (by simpa [hp] using hedge : (F.graph T).Reachable (.inr p) (.inr q)).trans hb⟩

theorem connected (hT : T.Connected) : (F.graph T).Connected := by
  have reach : ∀ x : B ⊕ P, ∃ b, (F.graph T).Reachable x (.inl b) := by
    rintro (b | p)
    · exact ⟨b,Reachable.refl _⟩
    · exact F.reaches_base T p
  let : Nonempty (B ⊕ P) := hT.nonempty.map Sum.inl
  refine ⟨fun x y => ?_⟩
  obtain ⟨a,ha⟩ := reach x
  obtain ⟨b,hb⟩ := reach y
  exact ha.trans (((hT a b).map (F.inclusion T)).trans hb.symm)

theorem lower_neighbor (p : P) (x : B ⊕ P)
    (h : (F.graph T).Adj (.inr p) x) (hr : F.rank x ≤ F.rank (.inr p)) :
    x = F.parent p := by
  cases x with
  | inl b => exact Eq.symm h
  | inr q =>
    rcases h with h | h
    · exact h.symm
    · have hd := F.decreases q p h
      simp only [rank] at hr
      omega

/-- Well-founded attachments preserve acyclicity, without any finiteness assumption. -/
theorem acyclic (hT : T.IsAcyclic) : (F.graph T).IsAcyclic := by
  classical
  intro x p hp
  obtain ⟨v,hv,hmax⟩ := p.support.toFinset.exists_max_image F.rank
    ⟨x,by simp⟩
  have hv' : v ∈ p.support := by simpa using hv
  have bound : ∀ y ∈ p.support, F.rank y ≤ F.rank v := by
    intro y hy
    exact hmax y (by simpa using hy)
  have hs : ∀ y ∈ p.support, y ∈ Set.range (Sum.inl : B → B ⊕ P) := by
    cases v with
    | inl b =>
      rintro (c | q) hy
      · exact ⟨c,rfl⟩
      · have h := bound (.inr q) hy
        simp only [rank] at h
        omega
    | inr q =>
      let w := p.rotate (.inr q) hv'
      have hw : w.IsCycle := hp.rotate hv'
      have hbound : ∀ y ∈ w.support, F.rank y ≤ F.rank (.inr q) := by
        intro y hy
        exact bound y ((p.mem_support_rotate_iff _ hv').mp hy)
      have h1 := F.lower_neighbor T q w.snd (w.adj_snd hw.not_nil)
        (hbound _ (w.getVert_mem_support 1))
      have h2 := F.lower_neighbor T q w.penultimate ((F.graph T).adj_symm (w.adj_penultimate hw.not_nil))
        (hbound _ (w.getVert_mem_support (w.length-1)))
      exact False.elim (hw.snd_ne_penultimate (h1.trans h2.symm))
  let S : Set (B ⊕ P) := Set.range Sum.inl
  let proj : (F.graph T).induce S →g T :=
    { toFun := fun v => Classical.choose v.prop
      map_rel' := by
        intro u v h
        change (F.graph T).Adj u.val v.val at h
        rw [← Classical.choose_spec u.prop,← Classical.choose_spec v.prop] at h
        exact h }
  have hinj : Function.Injective proj := by
    intro u v h
    apply Subtype.ext
    rw [← Classical.choose_spec u.prop,← Classical.choose_spec v.prop]
    exact congrArg Sum.inl h
  have hc : (p.induce S hs).IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map (f := (SimpleGraph.Embedding.induce S).toHom)
    simpa using hp
  exact hT ((p.induce S hs).map proj) (hc.map hinj)

theorem isTree (hT : T.IsTree) : (F.graph T).IsTree :=
  ⟨F.connected T hT.connected,F.acyclic T hT.isAcyclic⟩

end Graft
end TreewidthHom
