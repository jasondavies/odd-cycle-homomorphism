module

public import TreewidthHom.DirectionReduction
public import TreewidthHom.GraftDecomposition

@[expose] public section

/-!
# Width of the direction gadget

The gadget is a subdivision of K₄, so it has treewidth three. We use an explicit
ten-bag tree decomposition whose root bag contains both ports, and graft one copy
of it below a bag containing the endpoints of each replaced arc.
-/
namespace TreewidthHom.Arrow
open SimpleGraph

/-- Bags of a width-three decomposition of the gadget. Bag 0 holds both ports. -/
def gadgetBag : Fin 10 → Finset (Fin 13) :=
  ![{8,1,10,6},{10,1,6,5},{1,0,6,5},{9,8,6},{12,10,5},{11,10,12},{4,0,6},{2,0,4},{3,0,5},{7,6,5}]

/-- Parent pointers of the bag tree; bag 0 is the root. -/
def gadgetParent : Fin 10 → Fin 10 := ![0,0,1,0,1,4,2,6,2,1]

theorem gadgetParent_lt : ∀ i : Fin 10, i ≠ 0 → gadgetParent i < i := by decide

theorem gadgetBag_card : ∀ i, (gadgetBag i).card ≤ 4 := by decide

theorem gadgetBag_cover : ∀ u : Fin 13, ∃ i, u ∈ gadgetBag i := by decide

theorem gadgetBag_edge : ∀ u v : Fin 13, graph.Adj u v →
    ∃ i, u ∈ gadgetBag i ∧ v ∈ gadgetBag i := by decide

/-- A port occurring in a non-root bag also occurs in the parent bag. -/
theorem gadgetBag_port_up : ∀ i : Fin 10, i ≠ 0 →
    ((8 : Fin 13) ∈ gadgetBag i → (8 : Fin 13) ∈ gadgetBag (gadgetParent i)) ∧
    ((10 : Fin 13) ∈ gadgetBag i → (10 : Fin 13) ∈ gadgetBag (gadgetParent i)) := by decide

theorem gadgetBag_ports : (8 : Fin 13) ∈ gadgetBag 0 ∧ (10 : Fin 13) ∈ gadgetBag 0 := by decide

/-- Every gadget vertex has a unique topmost bag, so its bags form a subtree. -/
theorem gadgetBag_top : ∀ (u : Fin 13) (i j : Fin 10),
    u ∈ gadgetBag i → (i ≠ 0 → u ∉ gadgetBag (gadgetParent i)) →
    u ∈ gadgetBag j → (j ≠ 0 → u ∉ gadgetBag (gadgetParent j)) → i = j := by decide

namespace Assembly
variable {V E B : Type*} [DecidableEq V] [DecidableEq E]
variable (A : Assembly V E) {G : SimpleGraph V} {T : SimpleGraph B}
variable (D : Decomposition G T)

/-- One copy of the gadget's bag tree for each arc, rooted at a chosen old bag. -/
def copyGraft (parent : E → B) : Graft B (E × Fin 10) where
  parent p := if p.2 = 0 then .inl (parent p.1) else .inr (p.1,gadgetParent p.2)
  height p := p.2.val
  decreases := by
    intro p q h
    by_cases hp : p.2 = 0
    · simp [hp] at h
    · simp only [hp,↓reduceIte] at h
      have hq := Sum.inr.inj h
      subst q
      exact gadgetParent_lt p.2 hp

def copyBag (p : E × Fin 10) : Finset (AssemblyVertex V E) :=
  (gadgetBag p.2).image (A.embed p.1)

@[simp] theorem base_mem_copyBag (p : E × Fin 10) (v : V) :
    Sum.inl v ∈ A.copyBag p ↔
      ((8 : Fin 13) ∈ gadgetBag p.2 ∧ A.tail p.1 = v) ∨
      ((10 : Fin 13) ∈ gadgetBag p.2 ∧ A.head p.1 = v) := by
  simp only [copyBag,Finset.mem_image]
  constructor
  · rintro ⟨u,hu,he⟩
    by_cases h : u = 8
    · subst u
      left
      exact ⟨hu,by simpa using he⟩
    · by_cases h' : u = 10
      · subst u
        right
        exact ⟨hu,by simpa using he⟩
      · simp [embed,h,h'] at he
  · rintro (⟨hu,h⟩ | ⟨hu,h⟩)
    · exact ⟨8,hu,by simp [h]⟩
    · exact ⟨10,hu,by simp [h]⟩

@[simp] theorem private_mem_copyBag (p : E × Fin 10) (f : E) (u : Inner) :
    Sum.inr (f,u) ∈ A.copyBag p ↔ p.1 = f ∧ u.val ∈ gadgetBag p.2 := by
  simp only [copyBag,Finset.mem_image,A.embed_eq_inner_iff]
  constructor
  · rintro ⟨v,hv,he,rfl⟩
    exact ⟨he,hv⟩
  · rintro ⟨he,hu⟩
    exact ⟨u.val,hu,he,rfl⟩

theorem copyBag_card (p : E × Fin 10) : (A.copyBag p).card ≤ 3+1 :=
  Finset.card_image_le.trans (gadgetBag_card p.2)

/-- Graft a width-three gadget decomposition below a bag containing both ports. -/
noncomputable def extendDecomposition (parent : E → B)
    (hp : ∀ e, A.tail e ∈ D.bag (parent e) ∧ A.head e ∈ D.bag (parent e)) :
    Decomposition A.graph ((copyGraft parent).graph T) :=
  (copyGraft parent).extend D A.graph A.copyBag
    (by
      rintro ⟨f,u⟩
      obtain ⟨i,hi⟩ := gadgetBag_cover u.val
      exact ⟨(f,i),(A.private_mem_copyBag (f,i) f u).mpr ⟨rfl,hi⟩⟩)
    (by
      rintro x y ⟨e,u,v,h,rfl,rfl⟩
      obtain ⟨i,hu,hv⟩ := gadgetBag_edge u v h
      exact ⟨.inr (e,i),Finset.mem_image_of_mem _ hu,Finset.mem_image_of_mem _ hv⟩)
    (by
      rintro v ⟨e,i⟩ hv
      have hv' := (A.base_mem_copyBag (e,i) v).mp hv
      by_cases hi : i = 0
      · subst i
        have he : (copyGraft parent).parent (e,0) = Sum.inl (parent e) := by simp [copyGraft]
        rw [he,graftBag_inl_inl]
        rcases hv' with ⟨_,h⟩ | ⟨_,h⟩
        · exact h ▸ (hp e).1
        · exact h ▸ (hp e).2
      · have he : (copyGraft parent).parent (e,i) = Sum.inr (e,gadgetParent i) := by
          simp [copyGraft,hi]
        rw [he,graftBag_inr,base_mem_copyBag]
        have hup := gadgetBag_port_up i hi
        rcases hv' with ⟨h8,h⟩ | ⟨h10,h⟩
        · exact Or.inl ⟨hup.1 h8,h⟩
        · exact Or.inr ⟨hup.2 h10,h⟩)
    (by
      have key : ∀ (f : E) (u : Inner) (e : E) (i : Fin 10),
          Sum.inr (f,u) ∈ A.copyBag (e,i) →
          Sum.inr (f,u) ∉ graftBag D A.copyBag ((copyGraft parent).parent (e,i)) →
          e = f ∧ u.val ∈ gadgetBag i ∧ (i ≠ 0 → u.val ∉ gadgetBag (gadgetParent i)) := by
        intro f u e i hm hn
        have hm' := (A.private_mem_copyBag (e,i) f u).mp hm
        refine ⟨hm'.1,hm'.2,?_⟩
        intro hi hu
        apply hn
        have he : (copyGraft parent).parent (e,i) = Sum.inr (e,gadgetParent i) := by
          simp [copyGraft,hi]
        rw [he,graftBag_inr]
        exact (A.private_mem_copyBag (e,gadgetParent i) f u).mpr ⟨hm'.1,hu⟩
      rintro ⟨f,u⟩ ⟨e,i⟩ ⟨e',j⟩ hm hn hm' hn'
      obtain ⟨h1,h2,h3⟩ := key f u e i hm hn
      obtain ⟨h1',h2',h3'⟩ := key f u e' j hm' hn'
      have hij := gadgetBag_top u.val i j h2 h3 h2' h3'
      subst h1; subst h1'; subst hij
      rfl)

theorem extended_width (parent : E → B)
    (hp : ∀ e, A.tail e ∈ D.bag (parent e) ∧ A.head e ∈ D.bag (parent e))
    {k : ℕ} (hw : ∀ b, (D.bag b).card ≤ k + 1) :
    ∀ b, ((A.extendDecomposition D parent hp).bag b).card ≤ max k 3 + 1 :=
  graftBag_card D A.copyBag hw A.copyBag_card

end Assembly
end TreewidthHom.Arrow

namespace TreewidthHom.Digraph
open SimpleGraph
variable {V B : Type*} [DecidableEq V]

def underlying (D : Digraph V) : SimpleGraph V where
  Adj u v := D.edge u v ∨ D.edge v u
  symm := ⟨by intro u v h; exact h.elim Or.inr Or.inl⟩
  loopless := ⟨fun v h => h.elim (D.loopless v) (D.loopless v)⟩

/-- The direction gadget raises the width to at most max(k,3). -/
theorem directionReduction_width (D : Digraph V) {T : SimpleGraph B}
    (dec : Decomposition D.underlying T) {k : ℕ}
    (hw : ∀ b, (dec.bag b).card ≤ k + 1) :
    ∃ T' : SimpleGraph (B ⊕ (D.Arc × Fin 10)), ∃ dec' : Decomposition D.assembly.graph T',
      ∀ b, (dec'.bag b).card ≤ max k 3 + 1 := by
  classical
  have ports : ∀ e : D.Arc, ∃ b, e.val.1 ∈ dec.bag b ∧ e.val.2 ∈ dec.bag b :=
    fun e => dec.edge_cover (Or.inl e.prop)
  choose parent hp using ports
  exact ⟨_,D.assembly.extendDecomposition dec parent hp,
    D.assembly.extended_width dec parent hp hw⟩

end TreewidthHom.Digraph
