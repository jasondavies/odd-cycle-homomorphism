module

public import TreewidthHom.LeafTree
public import TreewidthHom.TreeDecomposition

@[expose] public section

namespace TreewidthHom
open SimpleGraph

/-- A general leaf-bag extension, with each new vertex confined to one leaf. -/
noncomputable def leafExtension {V P B E : Type*} [DecidableEq V] [DecidableEq P]
    {G : SimpleGraph V} {T : SimpleGraph B} (D : Decomposition G T)
    (H : SimpleGraph (V ⊕ P)) (parent : E → B) (owner : P → E)
    (bag : B ⊕ E → Finset (V ⊕ P))
    (old : ∀ v b, Sum.inl v ∈ bag (.inl b) ↔ v ∈ D.bag b)
    (priv : ∀ p b, Sum.inr p ∈ bag b ↔ b = Sum.inr (owner p))
    (base : ∀ v b, Sum.inl v ∈ bag b → v ∈ D.bag (Sum.elim id parent b))
    (edges : ∀ {u v}, H.Adj u v → ∃ b, u ∈ bag b ∧ v ∈ bag b) :
    Decomposition H (leafTree T parent) where
  tree := leafTree.isTree T parent D.tree
  bag := bag
  vertex_cover := by
    rintro (v | p)
    · obtain ⟨b,hb⟩ := D.vertex_cover v
      exact ⟨.inl b,(old v b).mpr hb⟩
    · exact ⟨.inr (owner p),(priv p _).mpr rfl⟩
  edge_cover := edges
  running := by
    rintro (v | p) a b ha hb
    · let home : B ⊕ E → B := Sum.elim id parent
      have toHome : ∀ x, Sum.inl v ∈ bag x →
          ∃ w : (leafTree T parent).Walk x (.inl (home x)), ∀ c ∈ w.support, Sum.inl v ∈ bag c := by
        rintro (c | e) hc
        · refine ⟨.nil,?_⟩
          intro d hd
          change d ∈ [Sum.inl c] at hd
          have he := List.mem_singleton.mp hd
          subst d
          exact hc
        · refine ⟨.cons (show (leafTree T parent).Adj (.inr e) (.inl (parent e)) from rfl) .nil,?_⟩
          intro d hd
          change d ∈ [Sum.inr e, Sum.inl (parent e)] at hd
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
          rcases hd with rfl | rfl
          · exact hc
          · exact (old v _).mpr (base v _ hc)
      obtain ⟨wa,hwa⟩ := toHome a ha
      obtain ⟨wb,hwb⟩ := toHome b hb
      obtain ⟨w,hw⟩ := D.running v (home a) (home b) (base v a ha) (base v b hb)
      let mid : (leafTree T parent).Walk (.inl (home a)) (.inl (home b)) :=
        w.map (leafTree.inclusion T parent)
      refine ⟨(wa.append mid).append wb.reverse,?_⟩
      intro c hc
      rcases (Walk.mem_support_append_iff _ _).mp hc with hc | hc
      · rcases (Walk.mem_support_append_iff _ _).mp hc with hc | hc
        · exact hwa c hc
        · have hc' : c ∈ w.support.map (leafTree.inclusion T parent) := by
            rw [← Walk.support_map]; exact hc
          obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc'
          exact (old v d).mpr (hw d hd)
      · rw [Walk.support_reverse,List.mem_reverse] at hc
        exact hwb c hc
    · have h1 := (priv p a).mp ha
      have h2 := (priv p b).mp hb
      subst a; subst b
      exact ⟨.nil,by simpa only [Walk.support_nil,List.mem_singleton,forall_eq] using ha⟩

end TreewidthHom
