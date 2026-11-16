module

public import TreewidthHom.GraftTree
public import TreewidthHom.TreeDecomposition

@[expose] public section

/-!
# Grafting small trees of bags onto a decomposition

A `Graft` attaches new bag indices below an existing decomposition tree by
well-founded parent pointers. Connectedness of a vertex's occurrence bags then
has a purely local criterion: climbing parent pointers while the vertex stays
in the bag must end either in the old tree or at one unique topmost new bag.
-/
namespace TreewidthHom
open SimpleGraph

namespace Graft
variable {B P W : Type*} (F : Graft B P) (T : SimpleGraph B)

/-- Climb parent pointers for as long as `x` remains in the parent bag. -/
theorem climb (bag : B ⊕ P → Finset W) (x : W) :
    ∀ n, ∀ a : B ⊕ P, F.rank a = n → x ∈ bag a →
      ∃ t : B ⊕ P, ∃ w : (F.graph T).Walk a t, (∀ c ∈ w.support, x ∈ bag c) ∧
        ∀ p, t = Sum.inr p → x ∉ bag (F.parent p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a hn ha
    cases a with
    | inl b =>
      refine ⟨.inl b,.nil,?_,?_⟩
      · intro c hc
        have he : c = Sum.inl b := by simpa using hc
        subst c
        exact ha
      · intro p hp
        cases hp
    | inr p =>
      by_cases hp : x ∈ bag (F.parent p)
      · have hlt : F.rank (F.parent p) < n := by
          subst hn
          cases hq : F.parent p with
          | inl b => simp [rank]
          | inr q =>
            have := F.decreases p q hq
            simp only [rank]
            omega
        obtain ⟨t,w,hw,ht⟩ := ih _ hlt (F.parent p) rfl hp
        refine ⟨t,.cons (F.parent_adj T p) w,?_,ht⟩
        intro c hc
        rw [Walk.support_cons,List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact ha
        · exact hw c hc
      · refine ⟨.inr p,.nil,?_,?_⟩
        · intro c hc
          have he : c = Sum.inr p := by simpa using hc
          subst c
          exact ha
        · intro q hq
          cases hq
          exact hp

/-- Local criterion for the connected-occurrence condition over a grafted tree. -/
theorem running_of_tops (bag : B ⊕ P → Finset W) (x : W)
    (hbase : ∀ a b : B, x ∈ bag (.inl a) → x ∈ bag (.inl b) →
      ∃ p : T.Walk a b, ∀ c ∈ p.support, x ∈ bag (.inl c))
    (hfree : ∀ p, x ∈ bag (.inr p) → x ∉ bag (F.parent p) → ∀ b, x ∉ bag (.inl b))
    (huniq : ∀ p q, x ∈ bag (.inr p) → x ∉ bag (F.parent p) →
      x ∈ bag (.inr q) → x ∉ bag (F.parent q) → p = q)
    (a b : B ⊕ P) (ha : x ∈ bag a) (hb : x ∈ bag b) :
    ∃ w : (F.graph T).Walk a b, ∀ c ∈ w.support, x ∈ bag c := by
  obtain ⟨ta,wa,hwa,hta⟩ := F.climb T bag x _ a rfl ha
  obtain ⟨tb,wb,hwb,htb⟩ := F.climb T bag x _ b rfl hb
  have hxa : x ∈ bag ta := hwa _ wa.end_mem_support
  have hxb : x ∈ bag tb := hwb _ wb.end_mem_support
  have glue : ∀ mid : (F.graph T).Walk ta tb, (∀ c ∈ mid.support, x ∈ bag c) →
      ∃ w : (F.graph T).Walk a b, ∀ c ∈ w.support, x ∈ bag c := by
    intro mid hmid
    refine ⟨(wa.append mid).append wb.reverse,?_⟩
    intro c hc
    rcases (Walk.mem_support_append_iff _ _).mp hc with hc | hc
    · rcases (Walk.mem_support_append_iff _ _).mp hc with hc | hc
      · exact hwa c hc
      · exact hmid c hc
    · rw [Walk.support_reverse,List.mem_reverse] at hc
      exact hwb c hc
  cases ta with
  | inl a' =>
    cases tb with
    | inl b' =>
      obtain ⟨p,hp⟩ := hbase a' b' hxa hxb
      apply glue (p.map (F.inclusion T))
      intro c hc
      have hc' : c ∈ p.support.map (F.inclusion T) := by
        rw [← Walk.support_map]; exact hc
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc'
      exact hp d hd
    | inr q => exact False.elim (hfree q hxb (htb q rfl) a' hxa)
  | inr p =>
    cases tb with
    | inl b' => exact False.elim (hfree p hxa (hta p rfl) b' hxb)
    | inr q =>
      have he := huniq p q hxa (hta p rfl) hxb (htb q rfl)
      subst q
      apply glue .nil
      intro c hc
      have he : c = Sum.inr p := by simpa using hc
      subst c
      exact hxa

end Graft

/-- Old bags are kept; each new index receives its own bag. -/
def graftBag {V Q B P : Type*} {G : SimpleGraph V} {T : SimpleGraph B} [DecidableEq V]
    (D : Decomposition G T) (newBag : P → Finset (V ⊕ Q)) : B ⊕ P → Finset (V ⊕ Q)
  | .inl b => (D.bag b).map ⟨Sum.inl,Sum.inl_injective⟩
  | .inr p => newBag p

section
variable {V Q B P : Type*} [DecidableEq V]
variable {G : SimpleGraph V} {T : SimpleGraph B}

@[simp] theorem graftBag_inl_inl (D : Decomposition G T) (newBag : P → Finset (V ⊕ Q))
    (v : V) (b : B) : Sum.inl v ∈ graftBag D newBag (.inl b) ↔ v ∈ D.bag b := by
  simp [graftBag]

@[simp] theorem graftBag_inr_inl (D : Decomposition G T) (newBag : P → Finset (V ⊕ Q))
    (q : Q) (b : B) : Sum.inr q ∉ graftBag D newBag (.inl b) := by
  simp [graftBag]

@[simp] theorem graftBag_inr (D : Decomposition G T) (newBag : P → Finset (V ⊕ Q))
    (p : P) : graftBag D newBag (.inr p) = newBag p := rfl

theorem graftBag_card (D : Decomposition G T) (newBag : P → Finset (V ⊕ Q)) {k m : ℕ}
    (hw : ∀ b, (D.bag b).card ≤ k+1) (hn : ∀ p, (newBag p).card ≤ m+1) :
    ∀ b, (graftBag D newBag b).card ≤ max k m+1 := by
  rintro (b | p)
  · have h := hw b
    simp only [graftBag,Finset.card_map]
    omega
  · have h := hn p
    change (newBag p).card ≤ _
    omega

/-- Extend a decomposition by grafted bags. Old vertices in a new bag must also
lie in its parent bag; every new vertex has a unique topmost bag. -/
noncomputable def Graft.extend [DecidableEq Q] (F : Graft B P) (D : Decomposition G T)
    (H : SimpleGraph (V ⊕ Q)) (newBag : P → Finset (V ⊕ Q))
    (cover : ∀ q, ∃ p, Sum.inr q ∈ newBag p)
    (edges : ∀ {u v}, H.Adj u v → ∃ b, u ∈ graftBag D newBag b ∧ v ∈ graftBag D newBag b)
    (base_up : ∀ v p, Sum.inl v ∈ newBag p → Sum.inl v ∈ graftBag D newBag (F.parent p))
    (top : ∀ q p p', Sum.inr q ∈ newBag p → Sum.inr q ∉ graftBag D newBag (F.parent p) →
      Sum.inr q ∈ newBag p' → Sum.inr q ∉ graftBag D newBag (F.parent p') → p = p') :
    Decomposition H (F.graph T) where
  tree := F.isTree T D.tree
  bag := graftBag D newBag
  vertex_cover := by
    rintro (v | q)
    · obtain ⟨b,hb⟩ := D.vertex_cover v
      exact ⟨.inl b,(graftBag_inl_inl D newBag v b).mpr hb⟩
    · obtain ⟨p,hp⟩ := cover q
      exact ⟨.inr p,hp⟩
  edge_cover := edges
  running := by
    rintro (v | q) a b ha hb
    · apply F.running_of_tops T (graftBag D newBag) (Sum.inl v) _ _ _ a b ha hb
      · intro a b ha hb
        obtain ⟨p,hp⟩ := D.running v a b ((graftBag_inl_inl D newBag v a).mp ha)
          ((graftBag_inl_inl D newBag v b).mp hb)
        exact ⟨p,fun c hc => (graftBag_inl_inl D newBag v c).mpr (hp c hc)⟩
      · intro p hp hn
        exact False.elim (hn (base_up v p hp))
      · intro p q hp hn
        exact False.elim (hn (base_up v p hp))
    · apply F.running_of_tops T (graftBag D newBag) (Sum.inr q) _ _ _ a b ha hb
      · intro a b ha
        exact False.elim (graftBag_inr_inl D newBag q a ha)
      · intro p _ _ b
        exact graftBag_inr_inl D newBag q b
      · intro p p' hp hn hp' hn'
        exact top q p p' hp hn hp' hn'

end

/-! ## Forests attached to a graph have width at most one more bag element -/
namespace Graft
variable {V P B : Type*} [DecidableEq V] [DecidableEq P]
variable (F : Graft V P) {G : SimpleGraph V} {T : SimpleGraph B}

/-- Move the attachment points of a graft from vertices to bags owning them. -/
def reindex (owner : V → B) : Graft B P where
  parent p := (F.parent p).map owner id
  height := F.height
  decreases := by
    intro p q h
    cases hp : F.parent p with
    | inl v => simp [hp] at h
    | inr r =>
      have hr : r = q := by simpa [hp] using h
      subst r
      exact F.decreases p q hp

/-- The bag of a new forest vertex: itself and its parent. -/
def linkBag (p : P) : Finset (V ⊕ P) := {Sum.inr p,F.parent p}

theorem linkBag_card (p : P) : (F.linkBag p).card ≤ 2 := Finset.card_le_two

/-- Attaching a forest by parent pointers needs only two-element new bags. -/
noncomputable def forestDecomposition (D : Decomposition G T) (owner : V → B)
    (ho : ∀ v, v ∈ D.bag (owner v)) :
    Decomposition (F.graph G) ((F.reindex owner).graph T) :=
  (F.reindex owner).extend D (F.graph G) F.linkBag
    (fun q => ⟨q,by simp [linkBag]⟩)
    (by
      rintro (u | u) (v | v) h
      · obtain ⟨b,hu,hv⟩ := D.edge_cover h
        exact ⟨.inl b,by simpa using hu,by simpa using hv⟩
      · have h' : F.parent v = Sum.inl u := h
        exact ⟨.inr v,by simp [linkBag,h'],by simp [linkBag]⟩
      · have h' : F.parent u = Sum.inl v := h
        exact ⟨.inr u,by simp [linkBag],by simp [linkBag,h']⟩
      · rcases h with h | h
        · exact ⟨.inr u,by simp [linkBag],by simp [linkBag,h]⟩
        · exact ⟨.inr v,by simp [linkBag,h],by simp [linkBag]⟩)
    (by
      intro v p hv
      have hp : F.parent p = Sum.inl v := by simpa [linkBag,eq_comm] using hv
      simpa [reindex,hp] using ho v)
    (by
      have key : ∀ q p, Sum.inr q ∈ F.linkBag p →
          Sum.inr q ∉ graftBag D F.linkBag ((F.reindex owner).parent p) → q = p := by
        intro q p hp hn
        have hq : q = p ∨ F.parent p = Sum.inr q := by simpa [linkBag,eq_comm] using hp
        rcases hq with h | h
        · exact h
        · exact False.elim (hn (by simp [reindex,h,linkBag]))
      intro q p p' hp hn hp' hn'
      exact (key q p hp hn).symm.trans (key q p' hp' hn'))

theorem forest_width (D : Decomposition G T) (owner : V → B)
    (ho : ∀ v, v ∈ D.bag (owner v)) {k : ℕ} (hw : ∀ b, (D.bag b).card ≤ k+1) :
    ∀ b, ((F.forestDecomposition D owner ho).bag b).card ≤ max k 1+1 :=
  graftBag_card D F.linkBag hw F.linkBag_card

end Graft
end TreewidthHom
