module

public import TreewidthHom.ListReduction

@[expose] public section

/-!
# Connectedness, degeneracy and girth of the source

A cycle of the source that meets the interior of a link traverses the whole
link and leaves its hub through a second link. A cycle that meets no link lies
in the reference cycles and contains one of them entirely.
-/
namespace TreewidthHom
open SimpleGraph

/-- Every nonempty finite set of vertices contains a vertex with at most `k`
neighbours in the set. -/
def IsDegenerate {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty →
    ∃ v ∈ S, ∃ N : Finset V, N.card ≤ k ∧ ∀ u ∈ S, G.Adj v u → u ∈ N

/-- A `k`-degenerate graph spans at most `2k|S|` ordered adjacent pairs in a set `S`. -/
theorem IsDegenerate.card_pairs_le {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (h : IsDegenerate G k) (S : Finset V) :
    ((S ×ˢ S).filter fun p : V × V => G.Adj p.1 p.2).card ≤ 2*k*S.card := by
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp
    obtain ⟨v,hv,N,hN,hadj⟩ := h S hS
    have hsub : ((S ×ˢ S).filter fun p : V × V => G.Adj p.1 p.2) ⊆
        (((S.erase v) ×ˢ (S.erase v)).filter fun p : V × V => G.Adj p.1 p.2) ∪
          (({v} : Finset V) ×ˢ N ∪ N ×ˢ ({v} : Finset V)) := by
      rintro ⟨x,y⟩ hp
      simp only [Finset.mem_filter,Finset.mem_product] at hp
      obtain ⟨⟨hx,hy⟩,hxy⟩ := hp
      simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_product,Finset.mem_erase,
        Finset.mem_singleton]
      by_cases h1 : x = v
      · subst h1
        exact Or.inr (Or.inl ⟨rfl,hadj y hy hxy⟩)
      · by_cases h2 : y = v
        · subst h2
          exact Or.inr (Or.inr ⟨hadj x hx hxy.symm,rfl⟩)
        · exact Or.inl ⟨⟨⟨h1,hx⟩,h2,hy⟩,hxy⟩
    have h1 := ih (S.erase v) (Finset.erase_ssubset hv)
    have h2 := Finset.card_le_card hsub
    have h3 := Finset.card_union_le
      (((S.erase v) ×ˢ (S.erase v)).filter fun p : V × V => G.Adj p.1 p.2)
      (({v} : Finset V) ×ˢ N ∪ N ×ˢ ({v} : Finset V))
    have h4 := Finset.card_union_le (({v} : Finset V) ×ˢ N) (N ×ˢ ({v} : Finset V))
    rw [Finset.card_product,Finset.card_product,Finset.card_singleton] at h4
    have h5 := Finset.card_erase_of_mem hv
    have h6 : 0 < S.card := Finset.card_pos.mpr hS
    have h7 : 2*k*S.card = 2*k*(S.erase v).card+2*k := by
      rw [h5]
      obtain ⟨c,hc⟩ : ∃ c, S.card = c+1 := ⟨S.card-1,by omega⟩
      rw [hc]
      simp [Nat.mul_add]
    omega

/-- A `k`-degenerate finite graph has at most `k|V|` edges. -/
theorem IsDegenerate.card_edgeSet_le {V : Type*} [Finite V] {G : SimpleGraph V} {k : ℕ}
    (h : IsDegenerate G k) : Nat.card G.edgeSet ≤ k*Nat.card V := by
  classical
  have := Fintype.ofFinite V
  have h1 := h.card_pairs_le Finset.univ
  have h2 : ∑ v, G.degree v =
      ((Finset.univ ×ˢ Finset.univ).filter fun p : V × V => G.Adj p.1 p.2).card := by
    rw [Finset.card_filter,Finset.sum_product]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.card_filter,← card_neighborFinset_eq_degree,neighborFinset_eq_filter]
  have h3 := G.sum_degrees_eq_twice_card_edges
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← edgeFinset_card]
  rw [Finset.card_univ] at h1
  have h4 : 2*k*Fintype.card V = 2*(k*Fintype.card V) := by ring
  omega

section Cycles
variable {V : Type*} {G : SimpleGraph V}

/-- Every vertex of a cycle has two distinct neighbours on the cycle. -/
theorem cycle_exists_two {v : V} {w : G.Walk v v} (hw : w.IsCycle) {x : V}
    (hx : x ∈ w.support) :
    ∃ a b, a ≠ b ∧ a ∈ w.support ∧ b ∈ w.support ∧ G.Adj x a ∧ G.Adj x b := by
  classical
  let p := w.rotate x hx
  have hp : p.IsCycle := hw.rotate hx
  have mem : ∀ y ∈ p.support, y ∈ w.support :=
    fun y hy => (w.mem_support_rotate_iff _ hx).mp hy
  exact ⟨p.snd,p.penultimate,hp.snd_ne_penultimate,mem _ (p.getVert_mem_support 1),
    mem _ (p.getVert_mem_support (p.length-1)),p.adj_snd hp.not_nil,
    (p.adj_penultimate hp.not_nil).symm⟩

/-- A cycle contains both candidates when a vertex has no other neighbour on it. -/
theorem cycle_two_neighbors {v : V} {w : G.Walk v v} (hw : w.IsCycle) {x a b : V}
    (hx : x ∈ w.support) (h : ∀ y ∈ w.support, G.Adj x y → y = a ∨ y = b) :
    a ∈ w.support ∧ b ∈ w.support := by
  obtain ⟨c,d,hne,hc,hd,ac,ad⟩ := cycle_exists_two hw hx
  rcases h c hc ac with rfl | rfl <;> rcases h d hd ad with rfl | rfl
  · exact absurd rfl hne
  · exact ⟨hc,hd⟩
  · exact ⟨hd,hc⟩
  · exact absurd rfl hne

/-- A closed walk is at least as long as any set of vertices it visits. -/
theorem card_le_length [DecidableEq V] {v : V} {w : G.Walk v v} (hw : ¬ w.Nil)
    (S : Finset V) (hS : ∀ x ∈ S, x ∈ w.support) : S.card ≤ w.length := by
  have hsub : S ⊆ w.support.tail.toFinset := by
    intro x hx
    rw [List.mem_toFinset]
    have h := hS x hx
    rw [← Walk.cons_tail_support] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact Walk.end_mem_tail_support hw
    · exact h
  calc S.card ≤ w.support.tail.toFinset.card := Finset.card_le_card hsub
    _ ≤ w.support.tail.length := List.toFinset_card_le _
    _ = w.length := by simp [Walk.length_support]

end Cycles

section Linked
variable {V L : Type*} {B : SimpleGraph V} {s t : L → V} {q : ℕ}

theorem linked_inner_reachable (l : L) (c : Fin q) :
    (linked B s t q).Reachable (.inl (s l)) (.inr (l,c)) := by
  obtain ⟨k,hk⟩ := c
  induction k with
  | zero =>
    exact Adj.reachable
      (show (linked B s t q).Adj (.inl (s l)) (.inr (l,⟨0,hk⟩)) from Or.inl ⟨rfl,rfl⟩)
  | succ k ih =>
    exact (ih (by omega)).trans (Adj.reachable
      (show (linked B s t q).Adj (.inr (l,⟨k,by omega⟩)) (.inr (l,⟨k+1,hk⟩)) from
        ⟨rfl,Or.inl rfl⟩))

theorem linked_ends_reachable (hq : 0 < q) (l : L) :
    (linked B s t q).Reachable (.inl (s l)) (.inl (t l)) :=
  (linked_inner_reachable l ⟨q-1,by omega⟩).trans (Adj.reachable
    (show (linked B s t q).Adj (.inr (l,⟨q-1,by omega⟩)) (.inl (t l)) from
      Or.inr ⟨by show q-1+1 = q; omega,rfl⟩))

/-- An inner vertex of a link has only its predecessor and successor as neighbours. -/
theorem linked_inner_adj (l : L) (k : ℕ) (hk : k < q) {y : V ⊕ (L × Fin q)}
    (h : (linked B s t q).Adj (.inr (l,⟨k,hk⟩)) y) :
    y = (if _ : k = 0 then .inl (s l) else .inr (l,⟨k-1,by omega⟩)) ∨
    y = (if _ : k+1 = q then .inl (t l) else .inr (l,⟨k+1,by omega⟩)) := by
  rcases y with u | ⟨l',⟨j,hj⟩⟩
  · rcases h with ⟨h0,rfl⟩ | ⟨h1,rfl⟩
    · have h0 : k = 0 := h0
      left; simp [h0]
    · have h1 : k+1 = q := h1
      right; simp [h1]
  · obtain ⟨rfl,h | h⟩ := h
    · have h : j = k+1 := h
      subst h
      have hne : ¬ k+1 = q := by omega
      right; simp [hne]
    · have h : k = j+1 := h
      subst h
      left; simp

/-- A cycle through an inner vertex of a link traverses the whole link. -/
theorem linked_cycle_link {v : V ⊕ (L × Fin q)} {w : (linked B s t q).Walk v v}
    (hw : w.IsCycle) {l : L} {c : Fin q} (h : .inr (l,c) ∈ w.support) :
    (∀ c' : Fin q, .inr (l,c') ∈ w.support) ∧ .inl (s l) ∈ w.support ∧
      .inl (t l) ∈ w.support := by
  let P : ℕ → Prop := fun k => ∃ hk : k < q, (.inr (l,⟨k,hk⟩) : V ⊕ (L × Fin q)) ∈ w.support
  have step := fun (k : ℕ) (hk : k < q)
      (hm : (.inr (l,⟨k,hk⟩) : V ⊕ (L × Fin q)) ∈ w.support) =>
    cycle_two_neighbors hw hm (fun y _ hy => linked_inner_adj l k hk hy)
  have down : ∀ k, P (k+1) → P k := by
    rintro k ⟨hk,hm⟩
    have h1 := (step (k+1) hk hm).1
    simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,↓reduceDIte,Nat.add_sub_cancel] at h1
    exact ⟨by omega,h1⟩
  have up : ∀ k, k+1 < q → P k → P (k+1) := by
    rintro k hk1 ⟨hk,hm⟩
    have h1 := (step k hk hm).2
    have hne : ¬ k+1 = q := by omega
    simp only [hne,↓reduceDIte] at h1
    exact ⟨hk1,h1⟩
  have h0 : P 0 := by
    have all : ∀ k, P k → P 0 := by
      intro k
      induction k with
      | zero => exact id
      | succ k ih => exact fun h => ih (down k h)
    exact all c.val ⟨c.isLt,h⟩
  have all : ∀ k, k < q → P k := by
    intro k
    induction k with
    | zero => exact fun _ => h0
    | succ k ih => exact fun hk => up k hk (ih (by omega))
  refine ⟨fun c' => (all c'.val c'.isLt).2,?_,?_⟩
  · obtain ⟨hk,hm⟩ := h0
    simpa using (step 0 hk hm).1
  · obtain ⟨hk,hm⟩ := all (q-1) (by have := c.isLt; omega)
    have h1 := (step (q-1) hk hm).2
    have he : q-1+1 = q := by omega
    simpa only [he,↓reduceDIte] using h1

/-- A cycle through a link whose end has no base edges has at least `q+3` vertices:
the link, its two ends, and the first vertex of a second link. -/
theorem linked_cycle_length {v : V ⊕ (L × Fin q)} {w : (linked B s t q).Walk v v}
    (hw : w.IsCycle) {l : L} {c : Fin q} (h : .inr (l,c) ∈ w.support)
    (hst : s l ≠ t l) (hiso : ∀ u, ¬ B.Adj (t l) u) : q+3 ≤ w.length := by
  classical
  obtain ⟨hin,hs,ht⟩ := linked_cycle_link hw h
  have hq : 0 < q := by have := c.isLt; omega
  obtain ⟨a,b,hne,ha,hb,aa,ab⟩ := cycle_exists_two hw ht
  have key : ∀ y, (linked B s t q).Adj (.inl (t l)) y → (∃ c', y = .inr (l,c')) →
      y = .inr (l,⟨q-1,by omega⟩) := by
    rintro (u | ⟨l',c'⟩) hadj ⟨c'',hy⟩
    · cases hy
    · cases hy
      rcases hadj with ⟨_,h1⟩ | ⟨h1,_⟩
      · exact absurd h1.symm hst
      · have : c' = ⟨q-1,by omega⟩ := Fin.ext (by show c'.val = q-1; omega)
        rw [this]
  have other : ∀ y, (linked B s t q).Adj (.inl (t l)) y → (¬ ∃ c', y = .inr (l,c')) →
      (∀ c', y ≠ .inr (l,c')) ∧ y ≠ .inl (s l) ∧ y ≠ .inl (t l) := by
    rintro (u | ⟨l',c'⟩) hadj hn
    · exact absurd hadj (hiso u)
    · exact ⟨fun c' hc => hn ⟨c',hc⟩,by simp,by simp⟩
  have hextra : ∃ x ∈ w.support, (∀ c', x ≠ .inr (l,c')) ∧ x ≠ .inl (s l) ∧ x ≠ .inl (t l) := by
    by_cases h1 : ∃ c', a = .inr (l,c')
    · by_cases h2 : ∃ c', b = .inr (l,c')
      · exact absurd ((key a aa h1).trans (key b ab h2).symm) hne
      · exact ⟨b,hb,other b ab h2⟩
    · exact ⟨a,ha,other a aa h1⟩
  obtain ⟨x,hx,hx1,hx2,hx3⟩ := hextra
  let inner : Finset (V ⊕ (L × Fin q)) :=
    Finset.univ.image (fun c' : Fin q => (.inr (l,c') : V ⊕ (L × Fin q)))
  have hinner : inner.card = q := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)]
    simp
  have h1 : (.inl (t l) : V ⊕ (L × Fin q)) ∉ inner := by simp [inner]
  have h2 : (.inl (s l) : V ⊕ (L × Fin q)) ∉ insert (.inl (t l)) inner := by
    simp [inner,hst]
  have h3 : x ∉ insert (.inl (s l)) (insert (.inl (t l)) inner) := by
    simp only [Finset.mem_insert,inner,Finset.mem_image,Finset.mem_univ,true_and,not_or,
      not_exists]
    exact ⟨hx2,hx3,fun c' hc => hx1 c' hc.symm⟩
  have hcard := card_le_length hw.not_nil
    (insert x (insert (.inl (s l)) (insert (.inl (t l)) inner))) (by
      intro y hy
      simp only [Finset.mem_insert,inner,Finset.mem_image,Finset.mem_univ,true_and] at hy
      rcases hy with rfl | rfl | rfl | ⟨c',rfl⟩
      · exact hx
      · exact hs
      · exact ht
      · exact hin c')
  rw [Finset.card_insert_of_notMem h3,Finset.card_insert_of_notMem h2,
    Finset.card_insert_of_notMem h1,hinner] at hcard
  exact hcard

end Linked

namespace OddCycle.ListReduction
open Reference
variable {m n : ℕ} [Fact (1 < n)]

theorem ref_of_val (i : Copies m n) {d : ZMod n} (hd : 2 ≤ d.val) :
    ref i d = .inr (i,⟨d.val-2,by have := ZMod.val_lt d; omega⟩) := by
  unfold ref
  split_ifs with h0 h1
  · omega
  · omega
  · rfl

omit [Fact (1 < n)] in
theorem val_natCast_lt {j : ℕ} (hj : j < n) : ((j : ℕ) : ZMod n).val = j := by
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt hj

theorem ref_natCast (i : Copies m n) (e : Fin (n-2)) :
    ref i ((e.val+2 : ℕ) : ZMod n) = .inr (i,e) := by
  have hv := val_natCast_lt (n := n) (j := e.val+2) (by have := e.isLt; omega)
  rw [ref_of_val i (by omega)]
  simp only [hv,Nat.add_sub_cancel]

/-- A private reference vertex has only its two cycle neighbours in the base graph. -/
theorem base_private_adj {i : Copies m n} {d : ZMod n} (hd : 2 ≤ d.val)
    {y : BaseVertex m n} (h : (base m n).Adj (.inl (ref i d)) y) :
    y = .inl (ref i (d+1)) ∨ y = .inl (ref i (d-1)) := by
  have hp := ref_of_val i hd
  have same : ∀ i' d', ref i d = ref i' d' → i = i' ∧ d = d' := by
    intro i' d' h1
    refine ⟨(ref_private (h1.symm.trans hp)).1,?_⟩
    simpa [coord_ref] using congrArg coord h1
  obtain ⟨_,h | h⟩ := (fromRel_adj _ _ _).mp h
  · rcases y with y | y
    · rcases h with ⟨h0,_⟩ | ⟨i',d',h1,rfl⟩
      · rw [hp] at h0
        cases h0
      · obtain ⟨rfl,rfl⟩ := same i' d' h1
        exact Or.inl rfl
    · exact h.elim
  · rcases y with y | y
    · rcases h with ⟨_,h0⟩ | ⟨i',d',rfl,h1⟩
      · rw [hp] at h0
        cases h0
      · obtain ⟨rfl,rfl⟩ := same i' (d'+1) h1
        right
        simp
    · exact h.elim

theorem src_ne_dst {F : SimpleGraph (Fin m)} {L : Fin m → Finset (ZMod n)} (l : Link F L) :
    src l.val ≠ dst l.val := by
  obtain ⟨(⟨v,d⟩ | ⟨u,v⟩),h⟩ := l
  · simp [src,dst]
  · have : u ≠ v := ne_of_lt h.1
    simpa [src,dst] using this

theorem dst_isolated {F : SimpleGraph (Fin m)} {L : Fin m → Finset (ZMod n)} (l : Link F L)
    (u : BaseVertex m n) : ¬ (base m n).Adj (dst l.val) u := by
  obtain ⟨(⟨v,d⟩ | ⟨u',v⟩),h⟩ := l <;>
  · intro hadj
    obtain ⟨_,h | h⟩ := (fromRel_adj _ _ _).mp hadj
    · exact h.elim
    · rcases u with u | u <;> exact h.elim

variable (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))

/-- Every cycle of the source has length at least the target length. -/
theorem source_cycle_length (hn : 5 ≤ n) {v : SourceVertex F L}
    {w : (source F L).Walk v v} (hw : w.IsCycle) : n ≤ w.length := by
  classical
  by_cases h1 : ∃ l c, (.inr (l,c) : SourceVertex F L) ∈ w.support
  · obtain ⟨l,c,h⟩ := h1
    have h := linked_cycle_length hw h (src_ne_dst l) (dst_isolated l)
    exact le_trans (by omega) h
  have nolink : ∀ y ∈ w.support, ∃ x, y = (.inl x : SourceVertex F L) := by
    rintro (x | ⟨l,c⟩) hy
    · exact ⟨x,rfl⟩
    · exact absurd ⟨l,c,hy⟩ h1
  have hpriv : ∃ i e, (.inl (.inl (.inr (i,e))) : SourceVertex F L) ∈ w.support := by
    obtain ⟨a,b,hne,ha,hb,aa,ab⟩ := cycle_exists_two hw w.start_mem_support
    obtain ⟨a,rfl⟩ := nolink a ha
    obtain ⟨b,rfl⟩ := nolink b hb
    obtain ⟨v,rfl⟩ := nolink v w.start_mem_support
    have aa : (base m n).Adj v a := aa
    have ab : (base m n).Adj v b := ab
    have inl : ∀ {x y : BaseVertex m n}, (base m n).Adj x y → ∃ r, y = .inl r := by
      intro x y h
      obtain ⟨_,h | h⟩ := (fromRel_adj _ _ _).mp h
      · rcases x with x | x <;> rcases y with y | y <;> first | exact ⟨_,rfl⟩ | exact h.elim
      · rcases x with x | x <;> rcases y with y | y <;> first | exact ⟨_,rfl⟩ | exact h.elim
    obtain ⟨ra,rfl⟩ := inl aa
    obtain ⟨rb,rfl⟩ := inl ab
    obtain ⟨rv,rfl⟩ := inl aa.symm
    rcases ra with ja | ⟨i,e⟩
    · rcases rb with jb | ⟨i,e⟩
      · rcases rv with jv | ⟨i,e⟩
        · exfalso
          have h1 : ja ≠ jv := fun h => aa.ne (by rw [h])
          have h2 : jb ≠ jv := fun h => ab.ne (by rw [h])
          have h3 : ja ≠ jb := fun h => hne (by rw [h])
          omega
        · exact ⟨i,e,w.start_mem_support⟩
      · exact ⟨i,e,hb⟩
    · exact ⟨i,e,ha⟩
  obtain ⟨i,e,he⟩ := hpriv
  let Q : ZMod n → Prop := fun d => (.inl (.inl (ref i d)) : SourceVertex F L) ∈ w.support
  have step : ∀ d : ZMod n, 2 ≤ d.val → Q d → Q (d+1) ∧ Q (d-1) := by
    intro d hd hq
    apply cycle_two_neighbors hw hq
    intro y hy hadj
    obtain ⟨y,rfl⟩ := nolink y hy
    rcases base_private_adj hd (show (base m n).Adj _ y from hadj) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have he2 : e.val+2 < n := by have := e.isLt; omega
  have start : Q ((e.val+2 : ℕ) : ZMod n) := by
    show (.inl (.inl (ref i _)) : SourceVertex F L) ∈ w.support
    rw [ref_natCast]
    exact he
  have up : ∀ j, e.val+2 ≤ j → j ≤ n → Q ((j : ℕ) : ZMod n) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact fun _ => start
    | succ j hj ih =>
      intro hjn
      have h := (step _ (by rw [val_natCast_lt (by omega)]; omega) (ih (by omega))).1
      simpa using h
  have down : ∀ k j, j+k = e.val+2 → 1 ≤ j → Q ((j : ℕ) : ZMod n) := by
    intro k
    induction k with
    | zero =>
      intro j hj _
      have : j = e.val+2 := by omega
      rw [this]
      exact start
    | succ k ih =>
      intro j hj hj1
      have h := (step _ (by rw [val_natCast_lt (by omega)]; omega)
        (ih (j+1) (by omega) (by omega))).2
      simpa using h
  have all : ∀ d : ZMod n, Q d := by
    intro d
    have hd := ZMod.val_lt d
    have hcast := ZMod.natCast_zmod_val d
    by_cases h0 : d.val = 0
    · have h := up n (by omega) le_rfl
      have hz : d = 0 := by rw [← hcast,h0]; simp
      rw [hz]
      simpa using h
    · rw [← hcast]
      by_cases hge : e.val+2 ≤ d.val
      · exact up _ hge (by omega)
      · exact down (e.val+2-d.val) _ (by omega) (by omega)
  let S : Finset (SourceVertex F L) :=
    Finset.univ.image (fun d : ZMod n => (.inl (.inl (ref i d)) : SourceVertex F L))
  have hcard : S.card = n := by
    rw [Finset.card_image_of_injective]
    · simp [ZMod.card]
    · intro a b hab
      have h := congrArg coord (Sum.inl.inj (Sum.inl.inj hab))
      simpa [coord_ref] using h
  have := card_le_length hw.not_nil S (by
    intro y hy
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hy
    exact all d)
  omega

/-- The source has girth at least the target length. -/
theorem source_le_egirth (hn : 5 ≤ n) : (n : ℕ∞) ≤ (source F L).egirth :=
  le_egirth.mpr fun _ w hw => by exact_mod_cast source_cycle_length F L hn hw

/-- Every reference cycle is a copy of the target inside the source. -/
theorem target_isContained (i : Copies m n) : (cyc n) ⊑ (source F L) := by
  refine ⟨⟨⟨fun d => .inl (.inl (ref i d)),?_⟩,?_⟩⟩
  · intro a b hab
    rcases (cyc_adj _ _).mp hab with rfl | rfl
    · exact base_ref_adj i a
    · exact (base_ref_adj i b).symm
  · intro a b hab
    have h := congrArg coord (Sum.inl.inj (Sum.inl.inj hab))
    simpa [coord_ref] using h

/-- With at least one input vertex, the girth is exactly the target length. -/
theorem source_egirth (hn : 5 ≤ n) (hm : 0 < m) : (source F L).egirth = n := by
  refine le_antisymm ?_ (source_le_egirth F L hn)
  refine (target_isContained F L (⟨0,hm⟩,0)).egirth_le.trans ?_
  obtain ⟨k,rfl⟩ : ∃ k, n = k+3 := ⟨n-3,by omega⟩
  rw [cyc_eq_cycleGraph (k+2)]
  have h := (cycleGraph.isCycle_cycle (n := k)).egirth_le_length
  rwa [cycleGraph.length_cycle] at h

/-- The source is 2-degenerate. -/
theorem source_degenerate : IsDegenerate (source F L) 2 := by
  classical
  intro S hS
  by_cases h1 : ∃ l c, (.inr (l,c) : SourceVertex F L) ∈ S
  · obtain ⟨l,⟨k,hk⟩,hm⟩ := h1
    obtain ⟨a,b,hab⟩ : ∃ a b, ∀ y, (source F L).Adj (.inr (l,⟨k,hk⟩)) y → y = a ∨ y = b :=
      ⟨_,_,fun y h => linked_inner_adj l k hk h⟩
    refine ⟨_,hm,{a,b},Finset.card_le_two,fun u _ hadj => ?_⟩
    rw [Finset.mem_insert,Finset.mem_singleton]
    exact hab u hadj
  have nolink : ∀ y ∈ S, ∃ x, y = (.inl x : SourceVertex F L) := by
    rintro (x | ⟨l,c⟩) hy
    · exact ⟨x,rfl⟩
    · exact absurd ⟨l,c,hy⟩ h1
  by_cases h2 : ∃ v, (.inl (.inr v) : SourceVertex F L) ∈ S
  · obtain ⟨v,hm⟩ := h2
    refine ⟨_,hm,∅,by simp,fun u hu hadj => ?_⟩
    obtain ⟨u,rfl⟩ := nolink u hu
    obtain ⟨_,h | h⟩ := (fromRel_adj _ _ _).mp (show (base m n).Adj (.inr v) u from hadj)
    · exact h.elim
    · rcases u with u | u <;> exact h.elim
  by_cases h3 : ∃ i e, (.inl (.inl (.inr (i,e))) : SourceVertex F L) ∈ S
  · obtain ⟨i,e,hm⟩ := h3
    have he2 : e.val+2 < n := by have := e.isLt; omega
    have hd : 2 ≤ ((e.val+2 : ℕ) : ZMod n).val := by rw [val_natCast_lt he2]; omega
    refine ⟨_,hm,{.inl (.inl (ref i (((e.val+2 : ℕ) : ZMod n)+1))),
      .inl (.inl (ref i (((e.val+2 : ℕ) : ZMod n)-1)))},Finset.card_le_two,fun u hu hadj => ?_⟩
    obtain ⟨u,rfl⟩ := nolink u hu
    rw [← ref_natCast i e] at hadj
    rw [Finset.mem_insert,Finset.mem_singleton]
    rcases base_private_adj hd (show (base m n).Adj _ u from hadj) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨v,hv⟩ := hS
  refine ⟨v,hv,{.inl (.inl (.inl 0)),.inl (.inl (.inl 1))},Finset.card_le_two,fun u hu _ => ?_⟩
  rw [Finset.mem_insert,Finset.mem_singleton]
  obtain ⟨u,rfl⟩ := nolink u hu
  rcases u with (j | ⟨i,e⟩) | u
  · have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact absurd ⟨i,e,hu⟩ h3
  · exact absurd ⟨u,hu⟩ h2

/-- If every list omits a residue, the source is connected. -/
theorem source_connected (hn : 5 ≤ n) (hL : ∀ v, ∃ d, d ∉ L v) : (source F L).Connected := by
  let A : SourceVertex F L := .inl (.inl (.inl 0))
  have hq : 0 < n-3 := by omega
  have href : ∀ i d, (source F L).Reachable A (.inl (.inl (ref i d))) := by
    intro i d
    have all : ∀ k : ℕ, (source F L).Reachable A (.inl (.inl (ref i (k : ZMod n)))) := by
      intro k
      induction k with
      | zero =>
        rw [Nat.cast_zero,ref_zero]
      | succ k ih =>
        refine ih.trans (Adj.reachable ?_)
        rw [Nat.cast_succ]
        exact base_ref_adj i _
    have h := all d.val
    rwa [ZMod.natCast_zmod_val] at h
  have hbase : ∀ r : RefVertex (Copies m n) n, (source F L).Reachable A (.inl (.inl r)) := by
    rintro (j | ⟨i,e⟩)
    · have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl
      · exact Reachable.refl _
      · exact Adj.reachable (show (base m n).Adj _ _ from base_anchor_adj)
    · rw [← ref_natCast i e]
      exact href i _
  have hhub : ∀ v, (source F L).Reachable A (.inl (.inr v)) := by
    intro v
    obtain ⟨d,hd⟩ := hL v
    exact (href (v,d) d).trans
      (linked_ends_reachable hq (⟨.inl (v,d),hd⟩ : Link F L))
  have hall : ∀ x, (source F L).Reachable A x := by
    rintro ((r | v) | ⟨l,c⟩)
    · exact hbase r
    · exact hhub v
    · refine Reachable.trans ?_ (linked_inner_reachable l c)
      rcases src l.val with r | v
      · exact hbase r
      · exact hhub v
  exact (connected_iff _).mpr ⟨fun x y => (hall x).symm.trans (hall y),⟨A⟩⟩

end OddCycle.ListReduction
end TreewidthHom
