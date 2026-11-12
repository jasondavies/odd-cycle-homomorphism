module

public import TreewidthHom.GraftTree
public import TreewidthHom.TreeDecomposition

@[expose] public section

namespace TreewidthHom
open SimpleGraph

/-- Parent chains rooted at specified old vertices. -/
structure RootedGraft (V P : Type*) extends Graft V P where
  root : P → V
  root_parent : ∀ p, Sum.elim id root (parent p) = root p

namespace RootedGraft
variable {V P B : Type*} [DecidableEq V] [DecidableEq P]
variable (F : RootedGraft V P) {G : SimpleGraph V} {T : SimpleGraph B}
variable (D : Decomposition G T) (owner : V → B) (ho : ∀ v, v ∈ D.bag (owner v))

/-- A parent forest, with each new vertex also joined to its old root. -/
def cone (G : SimpleGraph V) : SimpleGraph (V ⊕ P) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inl v, .inr p => F.root p = v
    | .inr p, .inl v => F.root p = v
    | .inr p, .inr q => F.parent p = .inr q ∨ F.parent q = .inr p
  symm := ⟨by
    rintro (u | u) (v | v) h
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact h.elim Or.inr Or.inl⟩
  loopless := ⟨by
    rintro (v | p) h
    · exact G.loopless.irrefl v h
    · rcases h with h | h <;> exact (Nat.lt_irrefl _) (F.decreases p p h)⟩

def indexGraft : Graft B P where
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

def newBag (p : P) : Finset (V ⊕ P) := {Sum.inl (F.root p),Sum.inr p,F.parent p}

def bag : B ⊕ P → Finset (V ⊕ P)
  | .inl b => (D.bag b).map ⟨Sum.inl,Sum.inl_injective⟩
  | .inr p => F.newBag p

@[simp] theorem base_old (v : V) (b : B) : Sum.inl v ∈ F.bag D (.inl b) ↔ v ∈ D.bag b := by
  simp [bag]

@[simp] theorem base_new (v : V) (p : P) : Sum.inl v ∈ F.newBag p ↔ F.root p = v := by
  have hr := F.root_parent p
  cases hp : F.parent p with
  | inl w =>
    have hh : w = F.root p := by simpa [hp] using hr
    simp [newBag,hp,hh,eq_comm]
  | inr q => simp [newBag,hp,eq_comm]

@[simp] theorem private_new (p q : P) :
    Sum.inr p ∈ F.newBag q ↔ p = q ∨ F.parent q = Sum.inr p := by
  simp [newBag,eq_comm]

@[simp] theorem own_private (p : P) : Sum.inr p ∈ F.newBag p := by simp
@[simp] theorem own_root (p : P) : Sum.inl (F.root p) ∈ F.newBag p := by simp

def home : B ⊕ P → B
  | .inl b => b
  | .inr p => owner (F.root p)

include ho in
theorem base_home (v : V) (b : B ⊕ P) (h : Sum.inl v ∈ F.bag D b) :
    v ∈ D.bag (F.home owner b) := by
  cases b with
  | inl b => exact (F.base_old D v b).mp h
  | inr p =>
    have hr := (F.base_new v p).mp h
    simpa [home,hr] using ho (F.root p)

include ho in
/-- Follow the parent chain while retaining its root in every bag. -/
theorem root_walk (p : P) :
    ∃ w : ((F.indexGraft owner).graph T).Walk (.inr p) (.inl (owner (F.root p))),
      ∀ b ∈ w.support, Sum.inl (F.root p) ∈ F.bag D b := by
  have main : ∀ n, ∀ p, F.height p = n →
      ∃ w : ((F.indexGraft owner).graph T).Walk (.inr p) (.inl (owner (F.root p))),
        ∀ b ∈ w.support, Sum.inl (F.root p) ∈ F.bag D b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      have he := (F.indexGraft owner).parent_adj T p
      have hr := F.root_parent p
      cases hp : F.parent p with
      | inl v =>
        have hv : v = F.root p := by simpa [hp] using hr
        have hedge : ((F.indexGraft owner).graph T).Adj (.inr p) (.inl (owner (F.root p))) := by
          simpa only [indexGraft,hp,Sum.map_inl,hv] using he
        refine ⟨.cons hedge .nil, ?_⟩
        intro b hb
        simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hb
        rcases hb with rfl | rfl
        · exact F.own_root p
        · exact (F.base_old D _ _).mpr (ho _)
      | inr q =>
        have hroot : F.root q = F.root p := by simpa [hp] using hr
        obtain ⟨w,hw⟩ := ih (F.height q) (by have := F.decreases p q hp; omega) q rfl
        have hedge : ((F.indexGraft owner).graph T).Adj (.inr p) (.inr q) := by
          simpa only [indexGraft,hp,Sum.map_inr,id_eq] using he
        rw [← hroot]
        refine ⟨.cons hedge w, ?_⟩
        intro b hb
        simp only [Walk.support_cons,List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact (F.base_new _ _).mpr hroot.symm
        · exact hw b hb
  exact main (F.height p) p rfl

include ho in
theorem base_to_home (v : V) (b : B ⊕ P) (hv : Sum.inl v ∈ F.bag D b) :
    ∃ w : ((F.indexGraft owner).graph T).Walk b (.inl (F.home owner b)),
      ∀ c ∈ w.support, Sum.inl v ∈ F.bag D c := by
  cases b with
  | inl b =>
    refine ⟨.nil,?_⟩
    intro c hc
    change c ∈ [Sum.inl b] at hc
    have he := List.mem_singleton.mp hc
    subst c
    exact hv
  | inr p =>
    have hr := (F.base_new v p).mp hv
    simpa only [home,hr] using F.root_walk D owner ho p

theorem private_to_own (p : P) (b : B ⊕ P) (hv : Sum.inr p ∈ F.bag D b) :
    ∃ w : ((F.indexGraft owner).graph T).Walk b (.inr p),
      ∀ c ∈ w.support, Sum.inr p ∈ F.bag D c := by
  cases b with
  | inl b => simp [bag] at hv
  | inr q =>
    rcases (F.private_new p q).mp hv with h | h
    · subst q
      exact ⟨.nil,by simpa only [Walk.support_nil,List.mem_singleton,forall_eq] using hv⟩
    · have hedge : ((F.indexGraft owner).graph T).Adj (.inr q) (.inr p) := by
        have he := (F.indexGraft owner).parent_adj T q
        simpa only [indexGraft,h,Sum.map_inr,id_eq] using he
      refine ⟨.cons hedge .nil, ?_⟩
      intro c hc
      simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl
      · exact hv
      · exact F.own_private p

noncomputable def decomposition : Decomposition (F.cone G) ((F.indexGraft owner).graph T) where
  tree := (F.indexGraft owner).isTree T D.tree
  bag := F.bag D
  vertex_cover := by
    rintro (v | p)
    · exact ⟨.inl (owner v),(F.base_old D v _).mpr (ho v)⟩
    · exact ⟨.inr p,F.own_private p⟩
  edge_cover := by
    rintro (u | u) (v | v) h
    · obtain ⟨b,hu,hv⟩ := D.edge_cover h
      exact ⟨.inl b,(F.base_old D u b).mpr hu,(F.base_old D v b).mpr hv⟩
    · exact ⟨.inr v,(F.base_new u v).mpr h,F.own_private v⟩
    · exact ⟨.inr u,F.own_private u,(F.base_new v u).mpr h⟩
    · rcases h with h | h
      · exact ⟨.inr u,F.own_private u,(F.private_new v u).mpr (Or.inr h)⟩
      · exact ⟨.inr v,(F.private_new u v).mpr (Or.inr h),F.own_private v⟩
  running := by
    rintro (v | p) a b ha hb
    · obtain ⟨wa,hwa⟩ := F.base_to_home D owner ho v a ha
      obtain ⟨wb,hwb⟩ := F.base_to_home D owner ho v b hb
      obtain ⟨w,hw⟩ := D.running v (F.home owner a) (F.home owner b)
        (F.base_home D owner ho v a ha) (F.base_home D owner ho v b hb)
      let mid : ((F.indexGraft owner).graph T).Walk (.inl (F.home owner a)) (.inl (F.home owner b)) :=
        w.map ((F.indexGraft owner).inclusion T)
      refine ⟨(wa.append mid).append wb.reverse,?_⟩
      intro c hc
      rcases (Walk.mem_support_append_iff _ _).mp hc with hc | hc
      · rcases (Walk.mem_support_append_iff _ _).mp hc with hc | hc
        · exact hwa c hc
        · have hc' : c ∈ w.support.map ((F.indexGraft owner).inclusion T) := by
            rw [← Walk.support_map]; exact hc
          obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc'
          exact (F.base_old D v d).mpr (hw d hd)
      · rw [Walk.support_reverse,List.mem_reverse] at hc
        exact hwb c hc
    · obtain ⟨wa,hwa⟩ := F.private_to_own D owner p a ha
      obtain ⟨wb,hwb⟩ := F.private_to_own D owner p b hb
      refine ⟨wa.append wb.reverse,?_⟩
      intro c hc
      rcases (Walk.mem_support_append_iff _ _).mp hc with hc | hc
      · exact hwa c hc
      · rw [Walk.support_reverse,List.mem_reverse] at hc
        exact hwb c hc

theorem width {k : ℕ} (hw : ∀ b, (D.bag b).card ≤ k+1) :
    ∀ b, (F.bag D b).card ≤ max k 2 + 1 := by
  rintro (b | p)
  · have h := hw b
    simp only [bag,Finset.card_map]
    omega
  · have h : (F.newBag p).card ≤ 3 := by
      unfold newBag
      have h1 := Finset.card_insert_le (Sum.inl (F.root p)) ({Sum.inr p,F.parent p} : Finset (V ⊕ P))
      have h2 := Finset.card_insert_le (Sum.inr p) ({F.parent p} : Finset (V ⊕ P))
      simp only [Finset.card_singleton] at h2
      omega
    change (F.newBag p).card ≤ _
    omega

end RootedGraft
end TreewidthHom
