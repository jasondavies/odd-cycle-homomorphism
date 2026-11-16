module

public import TreewidthHom.OddCycleReduction

@[expose] public section

/-!
# Chained Multicoloured Clique reduces to homomorphism into an odd cycle

Slots `0,...,K-1` are grouped into layers of `k` consecutive slots. Two slots are
constrained when they lie in one layer or in consecutive layers. Every slot has a
reference cycle and a choice cycle; all reference cycles share their vertices 0
and 1. Only a bounded number of hubs is needed at any time, which gives a width
bound depending on `k` alone. See `ODD_CYCLE.md`.
-/
namespace TreewidthHom.OddCycle.Chained
open SimpleGraph

variable {K N : ℕ}

/-- Slots `i < j` in the same layer or in consecutive layers of size `k`. -/
def Req (k : ℕ) (i j : Fin K) : Prop := j.val / k ≤ i.val / k + 1

/-- One vertex per slot, adjacent whenever the two slots are constrained. For
`K = r*k` this is Chained Multicoloured Clique with `r` layers and `k` colours. -/
def ChainedClique (k : ℕ) (Γ : SimpleGraph (Fin K × Fin N)) : Prop :=
  ∃ c : Fin K → Fin N, ∀ i j, i < j → Req k i j → Γ.Adj (i,c i) (j,c j)

/-! ## Reference cycles sharing one edge -/

/-- The two shared vertices, and the private vertices `2,...,n-1` of every copy. -/
abbrev RefVertex (K N : ℕ) := Fin 2 ⊕ (Fin K × Fin (cycleLength K N - 2))

/-- Vertex `d` of the reference cycle of slot `s`. -/
def ref (s : Fin K) (d : ZMod (cycleLength K N)) : RefVertex K N :=
  if h0 : d.val = 0 then .inl 0 else if h1 : d.val = 1 then .inl 1
  else .inr (s,⟨d.val-2,by have := ZMod.val_lt d; omega⟩)

/-- The coordinate of a reference vertex on its cycle. -/
def coord : RefVertex K N → ZMod (cycleLength K N)
  | .inl i => (i.val : ZMod (cycleLength K N))
  | .inr (_,e) => ((e.val+2 : ℕ) : ZMod (cycleLength K N))

@[simp] theorem ref_zero (s : Fin K) : ref (N := N) s 0 = .inl 0 := by simp [ref]

@[simp] theorem ref_one (s : Fin K) : ref (N := N) s 1 = .inl 1 := by
  simp [ref,ZMod.val_one]

theorem coord_ref (s : Fin K) (d : ZMod (cycleLength K N)) : coord (ref s d) = d := by
  have hd := ZMod.natCast_zmod_val d
  unfold ref
  split_ifs with h0 h1
  · rw [h0] at hd
    simpa [coord] using hd
  · rw [h1] at hd
    simpa [coord] using hd
  · have : d.val-2+2 = d.val := by omega
    simp only [coord,this,hd]

theorem ref_ne (s : Fin K) (d : ZMod (cycleLength K N)) : ref s d ≠ ref s (d+1) := by
  intro h
  have h' := congrArg coord h
  rw [coord_ref,coord_ref] at h'
  exact one_ne_zero (left_eq_add.mp h')

theorem ref_private {s s' : Fin K} {d : ZMod (cycleLength K N)}
    {e : Fin (cycleLength K N - 2)} (h : ref s d = .inr (s',e)) :
    s' = s ∧ d.val = e.val+2 := by
  unfold ref at h
  split_ifs at h with h0 h1
  have h2 := Sum.inr.inj h
  have h3 := congrArg (fun x : Fin K × Fin (cycleLength K N - 2) => x.2.val) h2
  have h4 := congrArg (fun x : Fin K × Fin (cycleLength K N - 2) => x.1) h2
  dsimp only at h3 h4
  exact ⟨h4.symm,by omega⟩

theorem ref_shared {s : Fin K} {d : ZMod (cycleLength K N)} {a : Fin 2}
    (h : ref (N := N) s d = .inl a) : d.val = a.val := by
  unfold ref at h
  split_ifs at h with h0 h1
  · rw [h0,← Sum.inl.inj h]; rfl
  · rw [h1,← Sum.inl.inj h]; rfl

/-! ## The source graph -/

abbrev BaseVertex (K N : ℕ) := RefVertex K N ⊕ (Fin K × ZMod (cycleLength K N))

/-- Forward steps of the reference cycles and of the choice cycles. -/
def BaseRel : BaseVertex K N → BaseVertex K N → Prop
  | .inl u, .inl v => ∃ s d, u = ref s d ∧ v = ref s (d+1)
  | .inr x, .inr y => x.1 = y.1 ∧ y.2 = x.2 + 1
  | _, _ => False

/-- The reference cycles, glued along one edge, and the disjoint choice cycles. -/
def base (K N : ℕ) : SimpleGraph (BaseVertex K N) := SimpleGraph.fromRel BaseRel

/-- Class links additionally carry nothing new; edge links exist for constrained
pairs of slots only. -/
def Valid (k : ℕ) (Γ : SimpleGraph (Fin K × Fin N)) : LinkCode K N → Prop
  | .inl (i,d) => ∀ a : Fin N, d ≠ (label i a : ZMod (cycleLength K N))
  | .inr (i,j,d) => (i < j ∧ Req k i j) ∧ ∀ a b : Fin N, Γ.Adj (i,a) (j,b) →
      d ≠ (label j b : ZMod (cycleLength K N)) - (label i a : ZMod (cycleLength K N))

/-- A class link starts on the slot's reference cycle, an edge link on the choice
cycle of the smaller slot. -/
def src : LinkCode K N → BaseVertex K N
  | .inl (i,d) => .inl (ref i d)
  | .inr (i,_,d) => .inr (i,d)

/-- Every link ends at the hub of a choice cycle. -/
def dst : LinkCode K N → BaseVertex K N
  | .inl (i,_) => .inr (i,0)
  | .inr (_,j,_) => .inr (j,0)

abbrev Link (k : ℕ) (Γ : SimpleGraph (Fin K × Fin N)) := {c : LinkCode K N // Valid k Γ c}

abbrev SourceVertex (k : ℕ) (Γ : SimpleGraph (Fin K × Fin N)) :=
  BaseVertex K N ⊕ (Link k Γ × Fin (cycleLength K N - 3))

def source (k : ℕ) (Γ : SimpleGraph (Fin K × Fin N)) : SimpleGraph (SourceVertex k Γ) :=
  linked (base K N) (fun l : Link k Γ => src l.val) (fun l => dst l.val) (cycleLength K N - 3)

/-! ## Correctness -/

theorem base_ref_adj (s : Fin K) (d : ZMod (cycleLength K N)) :
    (base K N).Adj (.inl (ref s d)) (.inl (ref s (d+1))) := by
  refine (SimpleGraph.fromRel_adj _ _ _).mpr ⟨?_,Or.inl ⟨s,d,rfl,rfl⟩⟩
  intro h
  exact ref_ne s d (Sum.inl.inj h)

theorem base_dial_adj (i : Fin K) (x : ZMod (cycleLength K N)) :
    (base K N).Adj (.inr (i,x)) (.inr (i,x+1)) := by
  refine (SimpleGraph.fromRel_adj _ _ _).mpr ⟨?_,Or.inl ⟨rfl,rfl⟩⟩
  intro h
  have h' := congrArg Prod.snd (Sum.inr.inj h)
  exact one_ne_zero (left_eq_add.mp h')

theorem source_hom_iff (k : ℕ) (Γ : SimpleGraph (Fin K × Fin N)) :
    Nonempty (source k Γ →g cyc (cycleLength K N)) ↔
      ∃ φ : base K N →g cyc (cycleLength K N),
        ∀ l : Link k Γ, φ (src l.val) ≠ φ (dst l.val) := by
  have h5 := five_le_cycleLength K N
  have hq : cycleLength K N - 3 + 1 = cycleLength K N - 2 := by omega
  unfold source
  rw [linked_hom_iff _ _ _ _ (by omega)]
  constructor
  · rintro ⟨φ,h⟩
    refine ⟨φ,fun l => ?_⟩
    obtain ⟨w,h0,h1,hs⟩ := h l
    rw [hq] at h1
    exact (walk_iff_ne (cycleLength_odd K N) (by omega) _ _).mp
      ⟨w,h0,h1,fun t ht => (cyc_adj _ _).mp (hs t (by omega))⟩
  · rintro ⟨φ,h⟩
    refine ⟨φ,fun l => ?_⟩
    obtain ⟨w,h0,h1,hs⟩ := (walk_iff_ne (cycleLength_odd K N) (by omega) _ _).mpr (h l)
    refine ⟨w,h0,?_,fun i hi => (cyc_adj _ _).mpr (hs i (by omega))⟩
    rw [hq]
    exact h1

theorem hom_of_clique (k : ℕ) (Γ : SimpleGraph (Fin K × Fin N)) (h : ChainedClique k Γ) :
    Nonempty (source k Γ →g cyc (cycleLength K N)) := by
  obtain ⟨c,hc⟩ := h
  rw [source_hom_iff]
  let f : BaseVertex K N → ZMod (cycleLength K N) := fun x => match x with
    | .inl u => coord u
    | .inr (i,a) => (label i (c i) : ZMod (cycleLength K N)) + a
  have hrel : ∀ x y, BaseRel x y → Near (f x) (f y) := by
    rintro (u | ⟨i,a⟩) (v | ⟨j,b⟩) hxy
    · obtain ⟨s,d,rfl,rfl⟩ := hxy
      change Near (coord (ref s d)) (coord (ref s (d+1)))
      rw [coord_ref,coord_ref]
      exact Or.inl rfl
    · exact hxy.elim
    · exact hxy.elim
    · obtain ⟨hij,hab⟩ : i = j ∧ b = a + 1 := hxy
      subst hij
      change Near (_ + a) (_ + b)
      have hn : Near a b := Or.inl hab
      exact hn.add_left _
  refine ⟨⟨f,?_⟩,?_⟩
  · intro x y hxy
    obtain ⟨_,h1 | h1⟩ := (SimpleGraph.fromRel_adj _ _ _).mp hxy
    · exact (cyc_adj _ _).mpr (hrel x y h1)
    · exact (cyc_adj _ _).mpr (hrel y x h1).symm
  · rintro ⟨(⟨i,d⟩ | ⟨i,j,d⟩),hv⟩
    · have hv' := hv (c i)
      change coord (ref i d) ≠ (label i (c i) : ZMod (cycleLength K N)) + 0
      rw [coord_ref,add_zero]
      exact hv'
    · obtain ⟨⟨hij,hreq⟩,hv'⟩ := hv
      change (label i (c i) : ZMod (cycleLength K N)) + d ≠ (label j (c j) : ZMod _) + 0
      rw [add_zero]
      intro he
      exact hv' (c i) (c j) (hc i j hij hreq) (by rw [← he]; ring)

theorem clique_of_hom (k : ℕ) (Γ : SimpleGraph (Fin K × Fin N))
    (h : Nonempty (source k Γ →g cyc (cycleLength K N))) : ChainedClique k Γ := by
  rw [source_hom_iff] at h
  obtain ⟨φ,hlink⟩ := h
  have href : ∀ s : Fin K, ∃ r ε : ZMod (cycleLength K N), (ε = 1 ∨ ε = -1) ∧
      ∀ x, φ (.inl (ref s x)) = r + ε*x := by
    intro s
    apply dial (cycleLength_odd K N) (fun x => φ (.inl (ref s x)))
    intro x
    exact (cyc_adj _ _).mp (φ.map_rel (base_ref_adj s x))
  choose ρ η hη href using href
  have hdial : ∀ i : Fin K, ∃ r ε : ZMod (cycleLength K N), (ε = 1 ∨ ε = -1) ∧
      ∀ x, φ (.inr (i,x)) = r + ε*x := by
    intro i
    apply dial (cycleLength_odd K N) (fun x => φ (.inr (i,x)))
    intro x
    exact (cyc_adj _ _).mp (φ.map_rel (base_dial_adj i x))
  choose r ε hε hf using hdial
  -- all reference cycles are placed identically, since they share two vertices
  have hρ : ∀ s t : Fin K, ρ s = ρ t := by
    intro s t
    have h1 := href s 0
    have h2 := href t 0
    rw [ref_zero] at h1 h2
    have := h1.symm.trans h2
    simpa using this
  have hηeq : ∀ s t : Fin K, η s = η t := by
    intro s t
    have h1 := href s 1
    have h2 := href t 1
    rw [ref_one] at h1 h2
    have h3 := h1.symm.trans h2
    rw [hρ s t] at h3
    simpa using h3
  have hsq : ∀ i, ε i * ε i = 1 := by
    intro i
    rcases hε i with h | h <;> rw [h] <;> ring
  have hsqη : ∀ s, η s * η s = 1 := by
    intro s
    rcases hη s with h | h <;> rw [h] <;> ring
  have hclass : ∀ i : Fin K, ∃ a : Fin N,
      η i * (r i - ρ i) = (label i a : ZMod (cycleLength K N)) := by
    intro i
    by_contra hno
    push Not at hno
    have hl := hlink ⟨.inl (i,η i * (r i - ρ i)),hno⟩
    apply hl
    change φ (.inl (ref i _)) = φ (.inr (i,0))
    rw [href,hf]
    linear_combination (r i - ρ i) * hsqη i
  choose a ha using hclass
  refine ⟨a,fun i j hij hreq => ?_⟩
  have hedge : ∃ a' b' : Fin N, Γ.Adj (i,a') (j,b') ∧
      ε i * (r j - r i) =
        (label j b' : ZMod (cycleLength K N)) - (label i a' : ZMod (cycleLength K N)) := by
    by_contra hno
    push Not at hno
    have hl := hlink ⟨.inr (i,j,ε i * (r j - r i)),⟨hij,hreq⟩,hno⟩
    apply hl
    change φ (.inr (i,_)) = φ (.inr (j,0))
    rw [hf,hf]
    linear_combination (r j - r i) * hsq i
  obtain ⟨a',b',hadj,heq⟩ := hedge
  have haj := ha j
  rw [hηeq j i,hρ j i] at haj
  have hr : r j - r i =
      η i * ((label j (a j) : ZMod (cycleLength K N)) - label i (a i)) := by
    linear_combination η i * (haj - ha i) - (r j - r i) * hsqη i
  rw [hr,← mul_assoc] at heq
  have hδ : ε i * η i = 1 ∨ ε i * η i = -1 := by
    rcases hε i with h1 | h1 <;> rcases hη i with h2 | h2 <;> rw [h1,h2] <;> simp
  obtain ⟨h1,h2⟩ := label_solve i j hij a' (a i) b' (a j) _ hδ heq
  rw [h1,h2]
  exact hadj

/-- Decision equivalence of the chained reduction. -/
theorem source_hom_iff_clique (k : ℕ) (Γ : SimpleGraph (Fin K × Fin N)) :
    Nonempty (source k Γ →g cyc (cycleLength K N)) ↔ ChainedClique k Γ :=
  ⟨clique_of_hom k Γ,hom_of_clique k Γ⟩

/-! ## Width: phases along the layers -/

section Width
variable (k : ℕ) (Γ : SimpleGraph (Fin K × Fin N))

/-- Retained base vertices: the two shared reference vertices and the hubs. -/
def bret : BaseVertex K N → Prop
  | .inl (.inl _) => True
  | .inl (.inr _) => False
  | .inr x => x.2 = 0

instance : DecidablePred (bret (K := K) (N := N)) := fun x => match x with
  | .inl (.inl _) => isTrue trivial
  | .inl (.inr _) => isFalse id
  | .inr x => inferInstanceAs (Decidable (x.2 = 0))

def ret : SourceVertex k Γ → Prop
  | .inl x => bret x
  | .inr _ => False

theorem dst_bret (c : LinkCode K N) : bret (dst c) := by
  rcases c with ⟨i,d⟩ | ⟨i,j,d⟩ <;> rfl

/-- The layer of a slot, as a phase. -/
def lay (i : Fin K) : Fin (K+1) :=
  ⟨i.val / k,by have := Nat.div_le_self i.val k; have := i.isLt; omega⟩

def linkLay : LinkCode K N → Fin (K+1)
  | .inl (i,_) => lay k i
  | .inr (i,_,_) => lay k i

def bph : BaseVertex K N → Fin (K+1)
  | .inl (.inl _) => 0
  | .inl (.inr (s,_)) => lay k s
  | .inr (i,_) => lay k i

/-- Every vertex that is not retained belongs to the phase of one layer. -/
def ph : SourceVertex k Γ → Fin (K+1)
  | .inl x => bph k x
  | .inr (l,_) => linkLay k l.val

/-- A retained vertex is kept during phase `t`: always for the shared vertices,
and for a hub during the phases of its own layer and of the layer before. -/
def binS (t : Fin (K+1)) : BaseVertex K N → Prop
  | .inl (.inl _) => True
  | .inl (.inr _) => False
  | .inr (i,_) => i.val / k = t.val ∨ i.val / k = t.val + 1

def inS (t : Fin (K+1)) : SourceVertex k Γ → Prop
  | .inl x => binS k t x
  | .inr _ => False

def par : SourceVertex k Γ → Option (SourceVertex k Γ)
  | .inl (.inl (.inl _)) => none
  | .inl (.inl (.inr (s,e))) =>
      if h : 0 < e.val then some (.inl (.inl (.inr (s,⟨e.val-1,by omega⟩)))) else none
  | .inl (.inr (i,a)) => if 1 < a.val then some (.inl (.inr (i,a-1))) else none
  | .inr (l,c) =>
      if hc : c.val = 0 then (if bret (src l.val) then none else some (.inl (src l.val)))
      else some (.inr (l,⟨c.val-1,by omega⟩))

def bht : BaseVertex K N → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr (_,e)) => e.val
  | .inr (_,a) => a.val

def ht : SourceVertex k Γ → ℕ
  | .inl x => bht x
  | .inr (_,c) => cycleLength K N + c.val

theorem bht_lt (x : BaseVertex K N) : bht x < cycleLength K N := by
  have h5 := five_le_cycleLength K N
  rcases x with (a | ⟨s,e⟩) | ⟨i,a⟩
  · change 0 < _; omega
  · have := e.isLt; change e.val < _; omega
  · exact ZMod.val_lt a

theorem bph_src (l : LinkCode K N) (h : ¬ bret (src l)) : bph k (src l) = linkLay k l := by
  rcases l with ⟨i,d⟩ | ⟨i,j,d⟩
  · change bph k (.inl (ref i d)) = lay k i
    rcases hr : ref i d with a | ⟨s,e⟩
    · exact absurd (by change bret (.inl (ref i d)); rw [hr]; trivial) h
    · obtain ⟨hs,_⟩ := ref_private hr
      rw [hs]
      rfl
  · rfl

theorem par_cases {v w : SourceVertex k Γ} (h : par k Γ v = some w) :
    ¬ ret k Γ w ∧ ht k Γ w < ht k Γ v ∧ ph k Γ w = ph k Γ v := by
  rcases v with ((a | ⟨s,e⟩) | ⟨i,a⟩) | ⟨l,c⟩
  · simp [par] at h
  · by_cases he : 0 < e.val
    · have hw : w = .inl (.inl (.inr (s,⟨e.val-1,by omega⟩))) := by simpa [par,he] using h.symm
      subst hw
      refine ⟨id,?_,rfl⟩
      change e.val-1 < e.val
      omega
    · simp [par,he] at h
  · by_cases ha : 1 < a.val
    · have hw : w = .inl (.inr (i,a-1)) := by simpa [par,ha] using h.symm
      subst hw
      refine ⟨sub_one_ne_zero ha,?_,rfl⟩
      have := val_sub_one (a := a) (by omega)
      change (a-1).val < a.val
      omega
    · simp [par,ha] at h
  · by_cases hc : c.val = 0
    · by_cases hs : bret (src l.val)
      · simp [par,hc,hs] at h
      · have hw : w = .inl (src l.val) := by simpa [par,hc,hs] using h.symm
        subst hw
        refine ⟨hs,?_,bph_src k l.val hs⟩
        have := bht_lt (src l.val)
        change bht (src l.val) < cycleLength K N + c.val
        omega
    · have hw : w = .inr (l,⟨c.val-1,by omega⟩) := by simpa [par,hc] using h.symm
      subst hw
      refine ⟨id,?_,rfl⟩
      change cycleLength K N + (c.val-1) < cycleLength K N + c.val
      omega

/-- A forward step between two vertices that are not retained is a parent pointer. -/
theorem par_of_rel {x y : BaseVertex K N} (hx : ¬ bret x) (hy : ¬ bret y) (h : BaseRel x y) :
    par k Γ (.inl y) = some (.inl x) := by
  rcases x with (a | ⟨s1,e1⟩) | ⟨i,a⟩
  · exact absurd trivial hx
  · rcases y with (b | ⟨s2,e2⟩) | ⟨j,b⟩
    · exact absurd trivial hy
    · obtain ⟨s,d,hu,hv⟩ : ∃ s d, Sum.inr (s1,e1) = ref (N := N) s d ∧
          Sum.inr (s2,e2) = ref s (d+1) := h
      obtain ⟨hs1,hd1⟩ := ref_private hu.symm
      obtain ⟨hs2,hd2⟩ := ref_private hv.symm
      have hval : (d+1).val = (d.val+1) % cycleLength K N := by
        rw [ZMod.val_add,ZMod.val_one]
      have hlt := ZMod.val_lt d
      have he : e2.val = e1.val+1 := by
        rcases Nat.lt_or_ge (d.val+1) (cycleLength K N) with h1 | h1
        · rw [Nat.mod_eq_of_lt h1] at hval
          omega
        · have h2 : d.val+1 = cycleLength K N := by omega
          rw [h2,Nat.mod_self] at hval
          omega
      have hpos : 0 < e2.val := by omega
      subst hs1; subst hs2
      simp only [par,hpos,↓reduceDIte,Option.some.injEq,Sum.inl.injEq,Sum.inr.injEq,
        Prod.mk.injEq,true_and]
      exact Fin.ext (by simp; omega)
    · exact h.elim
  · rcases y with (b | ⟨s2,e2⟩) | ⟨j,b⟩
    · exact absurd trivial hy
    · exact h.elim
    · obtain ⟨hij,hab⟩ : i = j ∧ b = a + 1 := h
      subst hij
      have hb2 := one_lt_val_of_succ hx hy hab
      have he : b - 1 = a := by rw [hab]; ring
      simp [par,hb2,he]

theorem par_edge {v w : SourceVertex k Γ} (hv : ¬ ret k Γ v) (hw : ¬ ret k Γ w)
    (h : (source k Γ).Adj v w) : par k Γ v = some w ∨ par k Γ w = some v := by
  rcases v with x | ⟨l,c⟩ <;> rcases w with y | ⟨l',c'⟩
  · obtain ⟨_,h1 | h1⟩ := (SimpleGraph.fromRel_adj _ _ _).mp (show (base K N).Adj x y from h)
    · exact Or.inr (par_of_rel k Γ hv hw h1)
    · exact Or.inl (par_of_rel k Γ hw hv h1)
  · have h' : (c'.val = 0 ∧ x = src l'.val) ∨
        (c'.val+1 = cycleLength K N - 3 ∧ x = dst l'.val) := h
    rcases h' with ⟨hc,hs⟩ | ⟨_,hd⟩
    · right
      have hne : ¬ bret (src l'.val) := by rw [← hs]; exact hv
      simp [par,hc,hne,hs]
    · exact absurd (by rw [hd]; exact dst_bret _) hv
  · have h' : (c.val = 0 ∧ y = src l.val) ∨
        (c.val+1 = cycleLength K N - 3 ∧ y = dst l.val) := h
    rcases h' with ⟨hc,hs⟩ | ⟨_,hd⟩
    · left
      have hne : ¬ bret (src l.val) := by rw [← hs]; exact hw
      simp [par,hc,hne,hs]
    · exact absurd (by rw [hd]; exact dst_bret _) hw
  · obtain ⟨hl,hcc⟩ : l = l' ∧ (c'.val = c.val+1 ∨ c.val = c'.val+1) := h
    subst hl
    rcases hcc with h1 | h1
    · right
      have h0 : c'.val ≠ 0 := by omega
      simp only [par,h0,↓reduceDIte,Option.some.injEq,Sum.inr.injEq,Prod.mk.injEq,true_and]
      exact Fin.ext (by simp; omega)
    · left
      have h0 : c.val ≠ 0 := by omega
      simp only [par,h0,↓reduceDIte,Option.some.injEq,Sum.inr.injEq,Prod.mk.injEq,true_and]
      exact Fin.ext (by simp; omega)

/-- A base edge from a vertex that is not retained to a retained one stays in phase. -/
theorem binS_of_rel {x y : BaseVertex K N} (hx : ¬ bret x) (hy : bret y)
    (h : BaseRel x y ∨ BaseRel y x) : binS k (bph k x) y := by
  rcases x with (a | ⟨s1,e1⟩) | ⟨i,a⟩
  · exact absurd trivial hx
  · rcases y with (b | ⟨s2,e2⟩) | ⟨j,b⟩
    · trivial
    · exact absurd hy id
    · rcases h with h | h <;> exact h.elim
  · rcases y with (b | ⟨s2,e2⟩) | ⟨j,b⟩
    · rcases h with h | h <;> exact h.elim
    · exact absurd hy id
    · have hij : i = j := by
        rcases h with h | h
        · exact h.1
        · exact h.1.symm
      subst hij
      exact Or.inl rfl

theorem binS_src (l : Link k Γ) (h : bret (src l.val)) :
    binS k (linkLay k l.val) (src l.val) := by
  rcases l with ⟨(⟨i,d⟩ | ⟨i,j,d⟩),hv⟩
  · change binS k _ (.inl (ref i d))
    rcases hr : ref i d with a | ⟨s,e⟩
    · trivial
    · exact absurd (by change bret (.inl (ref i d)) at h; rw [hr] at h; exact h) id
  · exact Or.inl rfl

theorem binS_dst (l : Link k Γ) : binS k (linkLay k l.val) (dst l.val) := by
  rcases l with ⟨(⟨i,d⟩ | ⟨i,j,d⟩),hv⟩
  · exact Or.inl rfl
  · obtain ⟨⟨hij,hreq⟩,_⟩ := hv
    have h1 : i.val / k ≤ j.val / k := Nat.div_le_div_right (Nat.le_of_lt hij)
    have h2 : j.val / k ≤ i.val / k + 1 := hreq
    change j.val / k = i.val / k ∨ j.val / k = i.val / k + 1
    omega

theorem mixed {p v : SourceVertex k Γ} (hp : ¬ ret k Γ p) (hv : ret k Γ v)
    (h : (source k Γ).Adj p v) : inS k Γ (ph k Γ p) v := by
  rcases p with x | ⟨l,c⟩ <;> rcases v with y | ⟨l',c'⟩
  · obtain ⟨_,h1⟩ := (SimpleGraph.fromRel_adj _ _ _).mp (show (base K N).Adj x y from h)
    exact binS_of_rel k hp hv h1
  · exact hv.elim
  · have h' : (c.val = 0 ∧ y = src l.val) ∨
        (c.val+1 = cycleLength K N - 3 ∧ y = dst l.val) := h
    rcases h' with ⟨_,hs⟩ | ⟨_,hd⟩
    · change binS k (linkLay k l.val) y
      rw [hs]
      exact binS_src k Γ l (by rw [← hs]; exact hv)
    · change binS k (linkLay k l.val) y
      rw [hd]
      exact binS_dst k Γ l
  · exact hv.elim

/-- The only edge between two retained vertices is the shared reference edge. -/
theorem retained_edge {u v : SourceVertex k Γ} (hu : ret k Γ u) (hv : ret k Γ v)
    (h : (source k Γ).Adj u v) : inS k Γ 0 u ∧ inS k Γ 0 v := by
  rcases u with x | ⟨l,c⟩
  · rcases v with y | ⟨l',c'⟩
    · obtain ⟨_,h1⟩ := (SimpleGraph.fromRel_adj _ _ _).mp (show (base K N).Adj x y from h)
      rcases x with (a | ⟨s1,e1⟩) | ⟨i,a⟩ <;> rcases y with (b | ⟨s2,e2⟩) | ⟨j,b⟩
      · exact ⟨trivial,trivial⟩
      · exact absurd hv id
      · rcases h1 with h1 | h1 <;> exact h1.elim
      · exact absurd hu id
      · exact absurd hu id
      · exact absurd hu id
      · rcases h1 with h1 | h1 <;> exact h1.elim
      · exact absurd hv id
      · have ha : a = 0 := hu
        have hb : b = 0 := hv
        subst ha; subst hb
        rcases h1 with h1 | h1
        · exact absurd h1.2.symm (by simp)
        · exact absurd h1.2.symm (by simp)
    · exact hv.elim
  · exact hu.elim

theorem inS_convex (v : SourceVertex k Γ) (a b c : Fin (K+1)) (hac : a ≤ c) (hcb : c ≤ b)
    (ha : inS k Γ a v) (hb : inS k Γ b v) : inS k Γ c v := by
  rcases v with ((x | y) | ⟨i,z⟩) | w
  · trivial
  · exact ha
  · have h1 : a.val ≤ c.val := hac
    have h2 : c.val ≤ b.val := hcb
    change i.val / k = a.val ∨ i.val / k = a.val + 1 at ha
    change i.val / k = b.val ∨ i.val / k = b.val + 1 at hb
    change i.val / k = c.val ∨ i.val / k = c.val + 1
    omega
  · exact ha

theorem inS_cover (v : SourceVertex k Γ) (hv : ret k Γ v) : ∃ t, inS k Γ t v := by
  rcases v with ((x | y) | ⟨i,z⟩) | w
  · exact ⟨0,trivial⟩
  · exact hv.elim
  · exact ⟨lay k i,Or.inl rfl⟩
  · exact hv.elim

/-- A layer has at most `k` slots. -/
theorem layer_card (hk : 0 < k) (t : ℕ) :
    (Finset.univ.filter (fun i : Fin K => i.val / k = t)).card ≤ k := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter (fun i : Fin K => i.val / k = t))
    (t := Finset.range k) (fun i => i.val % k)
    (fun i _ => Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ hk)))
    (by
      intro i hi j hj hij
      have hi' : i.val / k = t := by simpa using hi
      have hj' : j.val / k = t := by simpa using hj
      have e1 := Nat.div_add_mod i.val k
      have e2 := Nat.div_add_mod j.val k
      dsimp only at hij
      rw [hi'] at e1
      rw [hj'] at e2
      exact Fin.ext (by omega))
  simpa using h

/-- Names of the retained vertices, for counting them. -/
def code : SourceVertex k Γ → Fin 2 ⊕ Fin K
  | .inl (.inl (.inl a)) => .inl a
  | .inl (.inr (i,_)) => .inr i
  | _ => .inl 0

theorem code_injOn {u v : SourceVertex k Γ} (hu : ret k Γ u) (hv : ret k Γ v)
    (h : code k Γ u = code k Γ v) : u = v := by
  rcases u with ((a | y) | ⟨i,z⟩) | w
  · rcases v with ((b | y') | ⟨j,z'⟩) | w'
    · have hab : a = b := Sum.inl.inj h
      rw [hab]
    · exact hv.elim
    · cases h
    · exact hv.elim
  · exact hu.elim
  · rcases v with ((b | y') | ⟨j,z'⟩) | w'
    · cases h
    · exact hv.elim
    · have hij : i = j := Sum.inr.inj h
      have hz : z = 0 := hu
      have hz' : z' = 0 := hv
      rw [hij,hz,hz']
    · exact hv.elim
  · exact hu.elim

def parent (p : {v : SourceVertex k Γ // ¬ ret k Γ v}) :
    Option {v : SourceVertex k Γ // ¬ ret k Γ v} :=
  match h : par k Γ p.val with
  | none => none
  | some w => some ⟨w,(par_cases k Γ h).1⟩

theorem parent_eq_some (p q : {v : SourceVertex k Γ // ¬ ret k Γ v}) :
    parent k Γ p = some q ↔ par k Γ p.val = some q.val := by
  unfold parent
  split
  · rename_i h
    simp [h]
  · rename_i w h
    simp [h,Subtype.ext_iff]

noncomputable instance linkFintype : Fintype (Link k Γ) := by
  classical exact Subtype.fintype _

/-- The source has width at most `2k+3`, whatever the number of layers. -/
theorem source_width (hk : 0 < k) : HasWidth (source k Γ) (2*k+3) := by
  classical
  let S : Fin (K+1) → Finset {v : SourceVertex k Γ // ret k Γ v} := fun t =>
    Finset.univ.filter (fun v => inS k Γ t v.val)
  have hmem : ∀ t v, v ∈ S t ↔ inS k Γ t v.val := by
    intro t v
    simp [S]
  have hS : ∀ t, (S t).card ≤ 2*k+2 := by
    intro t
    let T : Finset (Fin 2 ⊕ Fin K) :=
      (Finset.univ : Finset (Fin 2)).map ⟨Sum.inl,Sum.inl_injective⟩ ∪
        ((Finset.univ.filter (fun i : Fin K => i.val / k = t.val)) ∪
          (Finset.univ.filter (fun i : Fin K => i.val / k = t.val + 1))).map
            ⟨Sum.inr,Sum.inr_injective⟩
    have hT : T.card ≤ 2*k+2 := by
      have h1 := Finset.card_union_le ((Finset.univ : Finset (Fin 2)).map ⟨Sum.inl,Sum.inl_injective⟩)
        (((Finset.univ.filter (fun i : Fin K => i.val / k = t.val)) ∪
          (Finset.univ.filter (fun i : Fin K => i.val / k = t.val + 1))).map
            ⟨Sum.inr,Sum.inr_injective⟩)
      have h2 := Finset.card_union_le (Finset.univ.filter (fun i : Fin K => i.val / k = t.val))
        (Finset.univ.filter (fun i : Fin K => i.val / k = t.val + 1))
      have h3 := layer_card (K := K) k hk t.val
      have h4 := layer_card (K := K) k hk (t.val+1)
      simp only [Finset.card_map,Finset.card_univ,Fintype.card_fin] at h1
      change T.card ≤ _ at h1
      omega
    refine le_trans (Finset.card_le_card_of_injOn (fun v => code k Γ v.val) ?_ ?_) hT
    · intro v hv
      have hin := (hmem t v).mp (Finset.mem_coe.mp hv)
      rcases v with ⟨((a | y) | ⟨i,z⟩) | w,hr⟩
      · simp [T,code]
      · exact hin.elim
      · have hin' : i.val / k = t.val ∨ i.val / k = t.val + 1 := hin
        simp [T,code,hin']
      · exact hin.elim
    · intro u _ v _ huv
      exact Subtype.ext (code_injOn k Γ u.prop v.prop huv)
  have h := hasWidth_of_phased_forest (source k Γ) (ret k Γ) K (2*k+2) S hS
    (fun v => by
      obtain ⟨t,ht⟩ := inS_cover k Γ v.val v.prop
      exact ⟨t,(hmem t v).mpr ht⟩)
    (fun v a b c hac hcb ha hb =>
      (hmem c v).mpr (inS_convex k Γ v.val a b c hac hcb ((hmem a v).mp ha) ((hmem b v).mp hb)))
    (fun u v hadj => by
      obtain ⟨h1,h2⟩ := retained_edge k Γ u.prop v.prop hadj
      exact ⟨0,(hmem 0 u).mpr h1,(hmem 0 v).mpr h2⟩)
    (fun p => ph k Γ p.val) (parent k Γ) (fun p => ht k Γ p.val)
    (fun p q hpq => (par_cases k Γ ((parent_eq_some k Γ p q).mp hpq)).2.1)
    (fun p q hpq => (par_cases k Γ ((parent_eq_some k Γ p q).mp hpq)).2.2)
    (fun p v hadj => (hmem _ v).mpr (mixed k Γ p.prop v.prop hadj))
    (fun p q hadj => (par_edge k Γ p.prop q.prop hadj).imp
      (parent_eq_some k Γ p q).mpr (parent_eq_some k Γ q p).mpr)
  exact h

/-! ## Size -/

theorem chained_size_arith (K n L : ℕ) (h5 : 5 ≤ n) (hL : L ≤ K*n + K*(K*n)) :
    2 + K*(n-2) + K*n + L*(n-3) ≤ 2*(K+1)^2*n^2 := by
  have h1 : L*(n-3) ≤ (K*n+K*(K*n))*n := Nat.mul_le_mul hL (by omega)
  have h2 : K*(n-2) ≤ K*n := Nat.mul_le_mul_left _ (by omega)
  have h3 : K*n ≤ K*n*n := Nat.le_mul_of_pos_right _ (by omega)
  have h4 : 2 ≤ 2*(n*n) := by nlinarith
  calc 2 + K*(n-2) + K*n + L*(n-3)
      ≤ 2*(n*n) + K*n*n + K*n*n + (K*n+K*(K*n))*n := by omega
    _ ≤ 2*(K+1)^2*n^2 := by nlinarith [Nat.zero_le (K*n*n)]

theorem source_card_le :
    Fintype.card (SourceVertex k Γ) ≤ 2*(K+1)^2*(cycleLength K N)^2 := by
  have hL : Fintype.card (Link k Γ) ≤ Fintype.card (LinkCode K N) := Fintype.card_subtype_le _
  have hC : Fintype.card (LinkCode K N) = K*cycleLength K N + K*(K*cycleLength K N) := by
    simp [LinkCode,ZMod.card]
  have hV : Fintype.card (SourceVertex k Γ) =
      2 + K*(cycleLength K N - 2) + K*cycleLength K N +
        Fintype.card (Link k Γ)*(cycleLength K N - 3) := by
    simp [SourceVertex,BaseVertex,RefVertex,ZMod.card]
  rw [hV]
  exact chained_size_arith K _ _ (five_le_cycleLength K N) (hC ▸ hL)

end Width

/-! ## Main theorem -/

/-- Chained Multicoloured Clique, with slots grouped into layers of `k`, reduces to
homomorphism into mathlib's cycle graph of odd length. The source width is at most
`2k+3` independently of the number of slots, and the target has width at most two. -/
theorem reduction (k : ℕ) (hk : 0 < k) (Γ : SimpleGraph (Fin K × Fin N)) :
    (Nonempty (source k Γ →g cycleGraph (cycleLength K N)) ↔ ChainedClique k Γ) ∧
    HasWidth (source k Γ) (2*k+3) ∧ HasWidth (cycleGraph (cycleLength K N)) 2 ∧
    Odd (cycleLength K N) ∧
    Fintype.card (SourceVertex k Γ) ≤ 2*(K+1)^2*(cycleLength K N)^2 := by
  have h1 := source_hom_iff_clique k Γ
  have h2 := target_width (cycleLength K N)
  rw [target_eq_cycleGraph] at h1 h2
  exact ⟨h1,source_width k Γ hk,h2,cycleLength_odd K N,source_card_le k Γ⟩

end TreewidthHom.OddCycle.Chained
