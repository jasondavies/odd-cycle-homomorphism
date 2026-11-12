module

public import TreewidthHom.DirectionReduction
public import TreewidthHom.TreeDecomposition
public import TreewidthHom.LeafTree

@[expose] public section

namespace TreewidthHom.Arrow.Assembly
open SimpleGraph
variable {V E B : Type*} [DecidableEq V] [DecidableEq E]
variable (A : Assembly V E) {G : SimpleGraph V} {T : SimpleGraph B}
variable (D : Decomposition G T)

def copyBag (e : E) : Finset (AssemblyVertex V E) := Finset.univ.image (A.embed e)

def extendedBag : B ⊕ E → Finset (AssemblyVertex V E)
  | .inl b => (D.bag b).map ⟨Sum.inl,Sum.inl_injective⟩
  | .inr e => A.copyBag e

@[simp] theorem base_mem_copyBag (e : E) (v : V) :
    Sum.inl v ∈ A.copyBag e ↔ A.tail e = v ∨ A.head e = v := by
  simp only [copyBag, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u,hu⟩
    by_cases h : u = 8
    · left; simpa [embed, h] using hu
    · by_cases h' : u = 10
      · right; simpa [embed, h, h'] using hu
      · simp [embed, h, h'] at hu
  · rintro (h | h)
    · exact ⟨8,by simp [h]⟩
    · exact ⟨10,by simp [h]⟩

@[simp] theorem private_mem_copyBag (e f : E) (u : Inner) :
    Sum.inr (f,u) ∈ A.copyBag e ↔ e = f := by
  simp [copyBag, A.embed_eq_inner_iff]

@[simp] theorem base_mem_oldBag (b : B) (v : V) :
    Sum.inl v ∈ A.extendedBag D (Sum.inl b) ↔ v ∈ D.bag b := by
  simp [extendedBag]

@[simp] theorem private_mem_extendedBag (b : B ⊕ E) (e : E) (u : Inner) :
    Sum.inr (e,u) ∈ A.extendedBag D b ↔ b = Sum.inr e := by
  cases b <;> simp [extendedBag]

def home (parent : E → B) : B ⊕ E → B := Sum.elim id parent

def toHome (parent : E → B) (b : B ⊕ E) :
    (leafTree T parent).Walk b (Sum.inl (home parent b)) :=
  match b with
  | .inl _ => .nil
  | .inr e => .cons (show (leafTree T parent).Adj (Sum.inr e) (Sum.inl (parent e)) from rfl) .nil

theorem base_mem_home (parent : E → B)
    (hp : ∀ e, A.tail e ∈ D.bag (parent e) ∧ A.head e ∈ D.bag (parent e))
    (v : V) (b : B ⊕ E) (hv : Sum.inl v ∈ A.extendedBag D b) :
    v ∈ D.bag (home parent b) := by
  cases b with
  | inl b => exact (A.base_mem_oldBag D b v).mp hv
  | inr e =>
    rcases (A.base_mem_copyBag e v).mp hv with h | h
    · simpa [home, ← h] using (hp e).1
    · simpa [home, ← h] using (hp e).2

theorem toHome_support (parent : E → B)
    (hp : ∀ e, A.tail e ∈ D.bag (parent e) ∧ A.head e ∈ D.bag (parent e))
    (v : V) (b : B ⊕ E) (hv : Sum.inl v ∈ A.extendedBag D b) :
    ∀ c ∈ (toHome (T := T) parent b).support, Sum.inl v ∈ A.extendedBag D c := by
  have hh := (A.base_mem_oldBag D (home parent b) v).mpr (A.base_mem_home D parent hp v b hv)
  cases b <;> simp_all [toHome, home]

/-- Attach one complete gadget bag as a leaf at a bag containing both ports. -/
noncomputable def extendDecomposition (parent : E → B)
    (hp : ∀ e, A.tail e ∈ D.bag (parent e) ∧ A.head e ∈ D.bag (parent e)) :
    Decomposition A.graph (leafTree T parent) where
  tree := leafTree.isTree T parent D.tree
  bag := A.extendedBag D
  vertex_cover := by
    rintro (v | ⟨e,u⟩)
    · obtain ⟨b,hb⟩ := D.vertex_cover v
      exact ⟨Sum.inl b,(A.base_mem_oldBag D b v).mpr hb⟩
    · exact ⟨Sum.inr e,by simp⟩
  edge_cover := by
    rintro x y ⟨e,u,v,_,rfl,rfl⟩
    refine ⟨Sum.inr e, ?_, ?_⟩ <;> simp [extendedBag, copyBag]
  running := by
    rintro (v | ⟨e,u⟩) a b ha hb
    · obtain ⟨p,hp'⟩ := D.running v (home parent a) (home parent b)
        (A.base_mem_home D parent hp v a ha) (A.base_mem_home D parent hp v b hb)
      let q : (leafTree T parent).Walk (Sum.inl (home parent a)) (Sum.inl (home parent b)) :=
        p.map (leafTree.inclusion T parent)
      refine ⟨((toHome parent a).append q).append (toHome parent b).reverse, ?_⟩
      intro c hc
      rcases (Walk.mem_support_append_iff _ _).mp hc with hc | hc
      · rcases (Walk.mem_support_append_iff _ _).mp hc with hc | hc
        · exact A.toHome_support D parent hp v a ha c hc
        · have hc' : c ∈ p.support.map (leafTree.inclusion T parent) := by
            rw [← Walk.support_map]
            exact hc
          obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc'
          exact (A.base_mem_oldBag D d v).mpr (hp' d hd)
      · exact A.toHome_support D parent hp v b hb c (by rw [Walk.support_reverse, List.mem_reverse] at hc; exact hc)
    · have h1 := (A.private_mem_extendedBag D a e u).mp ha
      have h2 := (A.private_mem_extendedBag D b e u).mp hb
      subst a; subst b
      exact ⟨.nil,by simpa only [Walk.support_nil, List.mem_singleton, forall_eq] using ha⟩

theorem extended_width {k : ℕ} (hw : ∀ b, (D.bag b).card ≤ k + 1) :
    ∀ b, (A.extendedBag D b).card ≤ max k 12 + 1 := by
  rintro (b | e)
  · have h := hw b
    simp only [extendedBag, Finset.card_map]
    omega
  · have h : (A.copyBag e).card ≤ 13 := by
      exact (Finset.card_image_le).trans (by simp)
    change (A.copyBag e).card ≤ _
    omega

end TreewidthHom.Arrow.Assembly

namespace TreewidthHom.Digraph
open SimpleGraph
variable {V B : Type*} [DecidableEq V]

def underlying (D : Digraph V) : SimpleGraph V where
  Adj u v := D.edge u v ∨ D.edge v u
  symm := ⟨by intro u v h; exact h.elim Or.inr Or.inl⟩
  loopless := ⟨fun v h => h.elim (D.loopless v) (D.loopless v)⟩

/-- The direction gadget raises the width to at most max(k,12). -/
theorem directionReduction_width (D : Digraph V) {T : SimpleGraph B}
    (dec : Decomposition D.underlying T) {k : ℕ}
    (hw : ∀ b, (dec.bag b).card ≤ k + 1) :
    ∃ T' : SimpleGraph (B ⊕ D.Arc), ∃ dec' : Decomposition D.assembly.graph T',
      ∀ b, (dec'.bag b).card ≤ max k 12 + 1 := by
  classical
  have ports : ∀ e : D.Arc, ∃ b, e.val.1 ∈ dec.bag b ∧ e.val.2 ∈ dec.bag b :=
    fun e => dec.edge_cover (Or.inl e.prop)
  choose parent hp using ports
  exact ⟨leafTree T parent, D.assembly.extendDecomposition dec parent hp,
    D.assembly.extended_width dec hw⟩

end TreewidthHom.Digraph
