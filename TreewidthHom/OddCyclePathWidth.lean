module

public import TreewidthHom.OddCycleChained
public import TreewidthHom.PathWidth

@[expose] public section

/-!
# Pathwidth of the odd cycle and of the two source graphs

The cycle has pathwidth at most two. The source of the plain reduction has
pathwidth at most `k+3`, and the source of the chained reduction at most `2k+4`.
In both sources the cycles are traversed one vertex at a time and every link is
swept while its starting vertex is the current one.
-/
namespace TreewidthHom.OddCycle
open SimpleGraph

/-- Bounding a finite set through an injective rank. -/
theorem card_le_of_rank {X : Type} (S : Finset X) (r : X → ℕ) (E : Finset ℕ)
    (hmem : ∀ x ∈ S, r x ∈ E) (hinj : ∀ x ∈ S, ∀ y ∈ S, r x = r y → x = y) :
    S.card ≤ E.card :=
  Finset.card_le_card_of_injOn r (fun x hx => hmem x hx) (fun x hx y hy h => hinj x hx y hy h)

theorem val_succ_of_ne_zero {n : ℕ} [Fact (1 < n)] {a b : ZMod n} (hb : b ≠ 0)
    (h : b = a + 1) : b.val = a.val + 1 := by
  have hn : NeZero n := ⟨by have := Fact.out (p := 1 < n); omega⟩
  have hval : b.val = (a.val+1) % n := by rw [h,ZMod.val_add,ZMod.val_one]
  have hlt := ZMod.val_lt a
  rcases Nat.lt_or_ge (a.val+1) n with h1 | h1
  · rwa [Nat.mod_eq_of_lt h1] at hval
  · have h2 : a.val+1 = n := by omega
    rw [h2,Nat.mod_self] at hval
    exact absurd ((ZMod.val_eq_zero b).mp hval) hb

/-- A cycle of length at least three has pathwidth at most two: keep vertex 0 and
slide a window of two consecutive vertices. -/
theorem target_pathWidth (n : ℕ) [Fact (1 < n)] (hn : 3 ≤ n) : HasPathWidth (cyc n) 2 := by
  classical
  have hne : NeZero n := ⟨by omega⟩
  let bag : Fin (n-3+1) → Finset (ZMod n) := fun τ =>
    Finset.univ.filter (fun a => a = 0 ∨ a.val = τ.val+1 ∨ a.val = τ.val+2)
  have hmem : ∀ a τ, a ∈ bag τ ↔ (a = 0 ∨ a.val = τ.val+1 ∨ a.val = τ.val+2) := by
    intro a τ
    simp [bag]
  let D : Decomposition (cyc n) (pathGraph (n-3+1)) :=
    intervalDecomposition (cyc n) (n-3) bag
      (by
        intro a
        have hlt := ZMod.val_lt a
        by_cases h0 : a = 0
        · exact ⟨0,(hmem a 0).mpr (Or.inl h0)⟩
        · have h1 : a.val ≠ 0 := fun h => h0 ((ZMod.val_eq_zero a).mp h)
          by_cases h2 : a.val = n-1
          · exact ⟨⟨n-3,by omega⟩,(hmem a _).mpr (Or.inr (Or.inr (by simp; omega)))⟩
          · exact ⟨⟨a.val-1,by omega⟩,(hmem a _).mpr (Or.inr (Or.inl (by simp; omega)))⟩)
      (by
        have key : ∀ a b : ZMod n, b = a + 1 → ∃ τ, a ∈ bag τ ∧ b ∈ bag τ := by
          intro a b hab
          have hlta := ZMod.val_lt a
          have hltb := ZMod.val_lt b
          by_cases ha : a = 0
          · have hb1 : b.val = 1 := by rw [hab,ha,zero_add,ZMod.val_one]
            exact ⟨⟨0,by omega⟩,(hmem a _).mpr (Or.inl ha),(hmem b _).mpr (Or.inr (Or.inl (by simp [hb1])))⟩
          · have ha1 : a.val ≠ 0 := fun h => ha ((ZMod.val_eq_zero a).mp h)
            by_cases hb : b = 0
            · have hval : (a.val+1) % n = 0 := by
                have := congrArg ZMod.val hab
                rw [hb,ZMod.val_zero,ZMod.val_add,ZMod.val_one] at this
                exact this.symm
              have han : a.val = n-1 := by
                rcases Nat.lt_or_ge (a.val+1) n with h1 | h1
                · rw [Nat.mod_eq_of_lt h1] at hval; omega
                · omega
              exact ⟨⟨n-3,by omega⟩,(hmem a _).mpr (Or.inr (Or.inr (by simp; omega))),
                (hmem b _).mpr (Or.inl hb)⟩
            · have hbv := val_succ_of_ne_zero hb hab
              exact ⟨⟨a.val-1,by omega⟩,(hmem a _).mpr (Or.inr (Or.inl (by simp; omega))),
                (hmem b _).mpr (Or.inr (Or.inr (by simp; omega)))⟩
        intro a b hadj
        rcases (cyc_adj a b).mp hadj with h | h
        · exact key a b h
        · obtain ⟨τ,h1,h2⟩ := key b a h
          exact ⟨τ,h2,h1⟩)
      (by
        intro a τ1 τ2 τ3 h13 h32 h1 h2
        have a1 := (hmem a τ1).mp h1
        have a2 := (hmem a τ2).mp h2
        have b1 : τ1.val ≤ τ3.val := h13
        have b2 : τ3.val ≤ τ2.val := h32
        refine (hmem a τ3).mpr ?_
        by_cases h0 : a = 0
        · exact Or.inl h0
        · right
          have a1' : a.val = τ1.val+1 ∨ a.val = τ1.val+2 := a1.resolve_left h0
          have a2' : a.val = τ2.val+1 ∨ a.val = τ2.val+2 := a2.resolve_left h0
          omega)
  refine ⟨inferInstance,n-3,D,fun τ => ?_⟩
  change (bag τ).card ≤ 3
  have hsub : bag τ ⊆ {0,((τ.val+1 : ℕ) : ZMod n),((τ.val+2 : ℕ) : ZMod n)} := by
    intro a ha
    rcases (hmem a τ).mp ha with h | h | h
    · simp [h]
    · have := ZMod.natCast_zmod_val a
      rw [h] at this
      simp [← this]
    · have := ZMod.natCast_zmod_val a
      rw [h] at this
      simp [← this]
  exact (Finset.card_le_card hsub).trans Finset.card_le_three

/-! ## The plain reduction -/

section Plain
variable {k N : ℕ} (Γ : SimpleGraph (Fin k × Fin N))

/-- Order of traversal: dial by dial, each in coordinate order. -/
def rank (x : DialVertex k N) : ℕ := x.1.val * cycleLength k N + x.2.val

theorem rank_injective : Function.Injective (rank (k := k) (N := N)) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  change i.val * cycleLength k N + a.val = j.val * cycleLength k N + b.val at h
  have h1 : (i.val * cycleLength k N + a.val) / cycleLength k N = i.val := by
    apply Nat.div_eq_of_lt_le
    · omega
    · have : (i.val+1) * cycleLength k N = i.val * cycleLength k N + cycleLength k N := by ring
      omega
  have h2 : (j.val * cycleLength k N + b.val) / cycleLength k N = j.val := by
    apply Nat.div_eq_of_lt_le
    · omega
    · have : (j.val+1) * cycleLength k N = j.val * cycleLength k N + cycleLength k N := by ring
      omega
  have hij : i.val = j.val := by rw [← h1,← h2,h]
  rw [hij] at h
  have hab : a.val = b.val := by omega
  exact Prod.ext (Fin.ext hij) (ZMod.val_injective _ hab)

/-- Number of positions. -/
def plainP (k N : ℕ) : ℕ := 2*((k+1)*cycleLength k N)+1

theorem rank_lt (x : DialVertex k N) : rank x < (k+1)*cycleLength k N := by
  have ha := ZMod.val_lt x.2
  have hi : x.1.val + 1 ≤ k+1 := x.1.isLt
  have h := Nat.mul_le_mul_right (cycleLength k N) hi
  have h2 : (x.1.val+1) * cycleLength k N = x.1.val * cycleLength k N + cycleLength k N := by ring
  unfold rank
  omega

/-- A hub is always present; any other vertex around its turn. -/
def plo (x : DialVertex k N) : ℕ := if x.2 = 0 then 0 else 2*rank x - 1
def phi (x : DialVertex k N) : ℕ := if x.2 = 0 then plainP k N else 2*rank x + 1

theorem plo_le_phi (x : DialVertex k N) : plo x ≤ phi x := by
  unfold plo phi
  split_ifs <;> omega

theorem phi_le (x : DialVertex k N) : phi x ≤ plainP k N := by
  have := rank_lt x
  unfold phi plainP
  split_ifs <;> omega

theorem plain_adj {x y : DialVertex k N} (h : (dials k N).Adj x y) :
    plo x ≤ phi y ∧ plo y ≤ phi x := by
  have key : ∀ x y : DialVertex k N, x.1 = y.1 → y.2 = x.2 + 1 →
      plo x ≤ phi y ∧ plo y ≤ phi x := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hij hab
    dsimp only at hij hab
    subst hij
    have hx := phi_le (i,a)
    have hy := phi_le (i,b)
    have hx' := plo_le_phi (i,a)
    have hy' := plo_le_phi (i,b)
    by_cases ha : a = 0
    · have h1 : plo (i,a) = 0 := by simp [plo,ha]
      have h2 : phi (i,a) = plainP k N := by simp [phi,ha]
      omega
    · by_cases hb : b = 0
      · have h1 : plo (i,b) = 0 := by simp [plo,hb]
        have h2 : phi (i,b) = plainP k N := by simp [phi,hb]
        omega
      · have hv := val_succ_of_ne_zero hb hab
        have hr : rank (i,b) = rank (i,a) + 1 := by
          unfold rank
          dsimp only
          omega
        simp only [plo,phi,ha,hb,↓reduceIte,hr]
        omega
  obtain ⟨hij,hab⟩ := h
  rcases (cyc_adj _ _).mp hab with h1 | h1
  · exact key x y hij h1
  · exact (key y x hij.symm h1).symm

def ppos (l : LinkCode k N) : ℕ := 2*rank (src l)

def pslot : LinkCode k N → ℕ
  | .inl (i,_) => i.val
  | .inr (_,j,_) => j.val

theorem pslot_lt (l : LinkCode k N) : pslot l < k := by
  rcases l with ⟨i,d⟩ | ⟨i,j,d⟩
  · exact i.isLt
  · exact j.isLt

theorem plain_link_inj (l l' : LinkCode k N) (hp : ppos l = ppos l') (hs : pslot l = pslot l') :
    l = l' := by
  have hsrc : src l = src l' := rank_injective (by unfold ppos at hp; omega)
  rcases l with ⟨i,d⟩ | ⟨i,j,d⟩ <;> rcases l' with ⟨i',d'⟩ | ⟨i',j',d'⟩
  · have hd : d = d' := congrArg Prod.snd hsrc
    have hi : i = i' := Fin.ext hs
    rw [hd,hi]
  · exact absurd (congrArg Prod.fst hsrc) (Fin.succ_ne_zero i').symm
  · exact absurd (congrArg Prod.fst hsrc) (Fin.succ_ne_zero i)
  · have hd : d = d' := congrArg Prod.snd hsrc
    have hi : i = i' := Fin.succ_injective _ (congrArg Prod.fst hsrc)
    have hj : j = j' := Fin.ext hs
    rw [hd,hi,hj]

theorem plain_present (x : DialVertex k N) : plo x ≤ 2*rank x ∧ 2*rank x ≤ phi x := by
  have := rank_lt x
  unfold plo phi plainP
  split_ifs <;> omega

theorem plain_hub_present (x : DialVertex k N) (hx : x.2 = 0) (p : ℕ) (hp : p ≤ plainP k N) :
    plo x ≤ p ∧ p ≤ phi x := by
  simp [plo,phi,hx,hp]

/-- At most `k+1` hubs and at most two other vertices are present at a position;
at an even position at most one other vertex. -/
theorem plain_count (p : ℕ) :
    (Finset.univ.filter (fun x : DialVertex k N => plo x ≤ p ∧ p ≤ phi x)).card ≤ k+3 ∧
    (p % 2 = 0 →
      (Finset.univ.filter (fun x : DialVertex k N => plo x ≤ p ∧ p ≤ phi x)).card ≤ k+2) := by
  let hubs : Finset (DialVertex k N) := Finset.univ.filter (fun x => x.2 = 0)
  let moving : Finset (DialVertex k N) :=
    Finset.univ.filter (fun x => x.2 ≠ 0 ∧ 2*rank x - 1 ≤ p ∧ p ≤ 2*rank x + 1)
  have hsub : Finset.univ.filter (fun x : DialVertex k N => plo x ≤ p ∧ p ≤ phi x) ⊆
      hubs ∪ moving := by
    intro x hx
    have hx' : plo x ≤ p ∧ p ≤ phi x := (Finset.mem_filter.mp hx).2
    by_cases h0 : x.2 = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h0⟩)
    · have h1 : 2*rank x - 1 ≤ p ∧ p ≤ 2*rank x + 1 := by
        unfold plo phi at hx'
        rwa [ite_eq_right h0,ite_eq_right h0] at hx'
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h0,h1⟩)
  have hhubs : hubs.card ≤ k+1 := by
    have h := card_le_of_rank hubs (fun x => x.1.val) (Finset.range (k+1))
      (fun x _ => Finset.mem_range.mpr x.1.isLt)
      (by
        intro x hx y hy hxy
        have hx0 : x.2 = 0 := (Finset.mem_filter.mp hx).2
        have hy0 : y.2 = 0 := (Finset.mem_filter.mp hy).2
        exact Prod.ext (Fin.ext hxy) (hx0.trans hy0.symm))
    simpa using h
  have hmoving : ∀ E : Finset ℕ, (∀ x ∈ moving, rank x ∈ E) → moving.card ≤ E.card :=
    fun E hE => card_le_of_rank moving rank E hE (fun x _ y _ h => rank_injective h)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  constructor
  · have h2 : moving.card ≤ 2 := by
      refine (hmoving {p/2,(p+1)/2} ?_).trans Finset.card_le_two
      intro x hx
      have hx' : x.2 ≠ 0 ∧ 2*rank x - 1 ≤ p ∧ p ≤ 2*rank x + 1 := (Finset.mem_filter.mp hx).2
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
    omega
  · intro hp
    have h1 : moving.card ≤ 1 := by
      refine (hmoving {p/2} ?_).trans (by simp)
      intro x hx
      have hx' : x.2 ≠ 0 ∧ 2*rank x - 1 ≤ p ∧ p ≤ 2*rank x + 1 := (Finset.mem_filter.mp hx).2
      simp only [Finset.mem_singleton]
      omega
    omega

/-- The source of the plain reduction has pathwidth at most `k+3`. -/
theorem source_pathWidth : HasPathWidth (source Γ) (k+3) := by
  have h5 := five_le_cycleLength k N
  refine hasPathWidth_linked (dials k N) (fun l : Link Γ => src l.val) (fun l => dst l.val)
    (cycleLength k N - 3) (by omega) (plainP k N) k (k+3) plo phi plo_le_phi phi_le
    (fun x y h => plain_adj h) (fun l => ppos l.val) (fun l => pslot l.val)
    (fun l => pslot_lt l.val)
    (fun l l' hp hs => Subtype.ext (plain_link_inj l.val l'.val hp hs))
    (fun l => plain_present (src l.val))
    (fun l => plain_hub_present (dst l.val) (dst_snd l.val) _
      ((plain_present (src l.val)).2.trans (phi_le _)))
    (fun p => by have := (plain_count (k := k) (N := N) p).1; omega)
    (fun l => by
      have := (plain_count (k := k) (N := N) (ppos l.val)).2 (by unfold ppos; omega)
      omega)

end Plain

/-! ## The chained reduction -/

namespace Chained
section ChainedPath
variable {K N : ℕ} (k : ℕ) (Γ : SimpleGraph (Fin K × Fin N))

theorem split_mul_add {q r q' r' n : ℕ} (hr : r < n) (hr' : r' < n) (h : q*n + r = q'*n + r') :
    q = q' ∧ r = r' := by
  have h1 : (q*n + r)/n = q := by
    apply Nat.div_eq_of_lt_le
    · omega
    · have : (q+1)*n = q*n + n := by ring
      omega
  have h2 : (q'*n + r')/n = q' := by
    apply Nat.div_eq_of_lt_le
    · omega
    · have : (q'+1)*n = q'*n + n := by ring
      omega
  have hq : q = q' := by rw [← h1,← h2,h]
  subst hq
  exact ⟨rfl,by omega⟩

/-- Positions used by one layer. -/
def layerSpan (k K N : ℕ) : ℕ := 4*cycleLength K N*k

def chainedP (k K N : ℕ) : ℕ := (K+1)*layerSpan k K N

/-- Order of traversal: slot by slot, the reference cycle before the choice cycle. -/
def crank : BaseVertex K N → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr (s,e)) => 2*s.val*cycleLength K N + (e.val+2)
  | .inr (s,a) => (2*s.val+1)*cycleLength K N + a.val

/-- The shared vertices are always present, a hub during the layer before its own
and its own layer, and any other vertex around its turn. -/
def clo : BaseVertex K N → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr (s,e)) => 2*crank (.inl (.inr (s,e))) - 1
  | .inr (s,a) => if a = 0 then (s.val/k - 1)*layerSpan k K N else 2*crank (.inr (s,a)) - 1

def chi : BaseVertex K N → ℕ
  | .inl (.inl _) => chainedP k K N
  | .inl (.inr (s,e)) => 2*crank (.inl (.inr (s,e))) + 1
  | .inr (s,a) => if a = 0 then (s.val/k + 1)*layerSpan k K N - 1 else 2*crank (.inr (s,a)) + 1

theorem layerSpan_pos (hk : 0 < k) : 0 < layerSpan k K N := by
  have h5 := five_le_cycleLength K N
  unfold layerSpan
  positivity

/-- The positions of a slot lie in the block of its layer. -/
theorem block_bounds (hk : 0 < k) (s : Fin K) :
    s.val/k*layerSpan k K N ≤ 4*s.val*cycleLength K N ∧
    4*(s.val+1)*cycleLength K N ≤ (s.val/k+1)*layerSpan k K N := by
  unfold layerSpan
  constructor
  · have h1 := Nat.mul_le_mul_left (4*cycleLength K N) (Nat.div_mul_le_self s.val k)
    have e1 : s.val/k*(4*cycleLength K N*k) = 4*cycleLength K N*(s.val/k*k) := by ring
    have e2 : 4*s.val*cycleLength K N = 4*cycleLength K N*s.val := by ring
    rw [e1,e2]
    exact h1
  · have h0 : s.val + 1 ≤ k*(s.val/k+1) := Nat.lt_mul_div_succ s.val hk
    have h1 := Nat.mul_le_mul_left (4*cycleLength K N) h0
    have e1 : (s.val/k+1)*(4*cycleLength K N*k) = 4*cycleLength K N*(k*(s.val/k+1)) := by ring
    have e2 : 4*(s.val+1)*cycleLength K N = 4*cycleLength K N*(s.val+1) := by ring
    rw [e1,e2]
    exact h1

theorem block_le_P (s : Fin K) : (s.val/k+1)*layerSpan k K N ≤ chainedP k K N := by
  unfold chainedP
  apply Nat.mul_le_mul_right
  have := Nat.div_le_self s.val k
  have := s.isLt
  omega

/-- A hub is present at every position of its own layer and of the layer before. -/
theorem hub_present (hk : 0 < k) (u : Fin K) (m lam : ℕ)
    (hlam : u.val/k = lam ∨ u.val/k = lam+1)
    (h1 : lam*layerSpan k K N ≤ m) (h2 : m+1 ≤ (lam+1)*layerSpan k K N) :
    clo k (.inr (u,0) : BaseVertex K N) ≤ m ∧ m ≤ chi k (.inr (u,0) : BaseVertex K N) := by
  have hW := layerSpan_pos (K := K) (N := N) k hk
  have e1 : (lam+1)*layerSpan k K N = lam*layerSpan k K N + layerSpan k K N := by ring
  have e2 : (lam+1+1)*layerSpan k K N = lam*layerSpan k K N + 2*layerSpan k K N := by ring
  simp only [clo,chi,↓reduceIte]
  rcases hlam with h | h
  · rw [h]
    have h3 : (lam-1)*layerSpan k K N ≤ lam*layerSpan k K N :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
  · rw [h,Nat.add_sub_cancel]
    omega

theorem clo_le_chi (hk : 0 < k) (x : BaseVertex K N) : clo k x ≤ chi k x := by
  rcases x with (a | ⟨s,e⟩) | ⟨s,a⟩
  · exact Nat.zero_le _
  · simp only [clo,chi]; omega
  · by_cases ha : a = 0
    · subst ha
      have hW := layerSpan_pos (K := K) (N := N) k hk
      have h3 : (s.val/k-1)*layerSpan k K N ≤ s.val/k*layerSpan k K N :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have e1 : (s.val/k+1)*layerSpan k K N = s.val/k*layerSpan k K N + layerSpan k K N := by ring
      simp only [clo,chi,↓reduceIte]
      omega
    · simp only [clo,chi,ha,↓reduceIte]; omega

/-- The positions around the turn of a vertex that is not retained, in its slot. -/
def slotOf : BaseVertex K N → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr (s,_)) => s.val
  | .inr (s,_) => s.val

theorem ranked_bounds (x : BaseVertex K N) (hx : ¬ bret x) :
    4*slotOf x*cycleLength K N + 1 ≤ 2*crank x ∧
    2*crank x + 2 ≤ 4*(slotOf x+1)*cycleLength K N := by
  have h5 := five_le_cycleLength K N
  rcases x with (a | ⟨s,e⟩) | ⟨s,a⟩
  · exact absurd trivial hx
  · have he := e.isLt
    have e1 : 4*s.val*cycleLength K N = 2*(2*s.val*cycleLength K N) := by ring
    have e2 : 4*(s.val+1)*cycleLength K N = 2*(2*s.val*cycleLength K N) + 4*cycleLength K N := by
      ring
    simp only [crank,slotOf]
    omega
  · have ha0 : a ≠ 0 := hx
    have ha1 : a.val ≠ 0 := fun h => ha0 ((ZMod.val_eq_zero a).mp h)
    have ha := ZMod.val_lt a
    have e1 : 4*s.val*cycleLength K N = 2*(2*s.val*cycleLength K N) := by ring
    have e2 : 4*(s.val+1)*cycleLength K N = 2*(2*s.val*cycleLength K N) + 4*cycleLength K N := by
      ring
    have e3 : (2*s.val+1)*cycleLength K N = 2*s.val*cycleLength K N + cycleLength K N := by ring
    simp only [crank,slotOf]
    omega

theorem ranked_lo_hi (x : BaseVertex K N) (hx : ¬ bret x) :
    clo k x = 2*crank x - 1 ∧ chi k x = 2*crank x + 1 := by
  rcases x with (a | ⟨s,e⟩) | ⟨s,a⟩
  · exact absurd trivial hx
  · exact ⟨rfl,rfl⟩
  · have ha0 : a ≠ 0 := hx
    simp [clo,chi,ha0]

theorem chi_le (hk : 0 < k) (x : BaseVertex K N) : chi k x ≤ chainedP k K N := by
  rcases x with (a | ⟨s,e⟩) | ⟨s,a⟩
  · exact le_rfl
  · have h1 := ranked_bounds (.inl (.inr (s,e)) : BaseVertex K N) id
    have h2 := (block_bounds (N := N) k hk s).2
    have h3 := block_le_P (N := N) k s
    simp only [slotOf] at h1
    simp only [chi]
    omega
  · by_cases ha : a = 0
    · have h3 := block_le_P (N := N) k s
      simp only [chi,ha,↓reduceIte]
      omega
    · have h1 := ranked_bounds (.inr (s,a) : BaseVertex K N) ha
      have h2 := (block_bounds (N := N) k hk s).2
      have h3 := block_le_P (N := N) k s
      simp only [slotOf] at h1
      simp only [chi,ha,↓reduceIte]
      omega

/-- A vertex that is not retained and the hub of a slot in its layer or the next
layer are present together. -/
theorem hub_ranked (hk : 0 < k) (u : Fin K) (x : BaseVertex K N) (hx : ¬ bret x)
    (hlay : u.val/k = slotOf x/k ∨ u.val/k = slotOf x/k+1) (hs : slotOf x < K) :
    (clo k (.inr (u,0) : BaseVertex K N) ≤ chi k x ∧ clo k x ≤ chi k (.inr (u,0) : BaseVertex K N)) := by
  obtain ⟨h1,h2⟩ := ranked_bounds x hx
  obtain ⟨b1,b2⟩ := block_bounds (N := N) k hk ⟨slotOf x,hs⟩
  obtain ⟨l1,l2⟩ := ranked_lo_hi k x hx
  dsimp only at b1 b2
  have p1 := hub_present (N := N) k hk u (2*crank x - 1) (slotOf x/k) hlay (by omega) (by omega)
  have p2 := hub_present (N := N) k hk u (2*crank x + 1) (slotOf x/k) hlay (by omega) (by omega)
  rw [l1,l2]
  exact ⟨p2.1,p1.2⟩

theorem slotOf_lt (x : BaseVertex K N) (hx : ¬ bret x) : slotOf x < K := by
  rcases x with (a | ⟨s,e⟩) | ⟨s,a⟩
  · exact absurd trivial hx
  · exact s.isLt
  · exact s.isLt

theorem chained_rel (hk : 0 < k) {x y : BaseVertex K N} (h : BaseRel x y) :
    clo k x ≤ chi k y ∧ clo k y ≤ chi k x := by
  have hxP := chi_le k hk x
  have hyP := chi_le k hk y
  have hx' := clo_le_chi k hk x
  have hy' := clo_le_chi k hk y
  rcases x with (a | ⟨s1,e1⟩) | ⟨i,a⟩
  · have h1 : clo k (.inl (.inl a) : BaseVertex K N) = 0 := rfl
    have h2 : chi k (.inl (.inl a) : BaseVertex K N) = chainedP k K N := rfl
    omega
  · rcases y with (b | ⟨s2,e2⟩) | ⟨j,b⟩
    · have h1 : clo k (.inl (.inl b) : BaseVertex K N) = 0 := rfl
      have h2 : chi k (.inl (.inl b) : BaseVertex K N) = chainedP k K N := rfl
      omega
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
      subst hs1; subst hs2
      simp only [clo,chi,crank]
      omega
    · exact h.elim
  · rcases y with (b | ⟨s2,e2⟩) | ⟨j,b⟩
    · have h1 : clo k (.inl (.inl b) : BaseVertex K N) = 0 := rfl
      have h2 : chi k (.inl (.inl b) : BaseVertex K N) = chainedP k K N := rfl
      omega
    · exact h.elim
    · obtain ⟨hij,hab⟩ : i = j ∧ b = a + 1 := h
      subst hij
      by_cases ha : a = 0
      · have hb : b ≠ 0 := by
          rw [hab,ha,zero_add]
          exact one_ne_zero
        subst ha
        have := hub_ranked k hk i (.inr (i,b)) hb (Or.inl rfl) i.isLt
        exact ⟨this.1,this.2⟩
      · by_cases hb : b = 0
        · subst hb
          have := hub_ranked k hk i (.inr (i,a)) ha (Or.inl rfl) i.isLt
          exact ⟨this.2,this.1⟩
        · have hv := val_succ_of_ne_zero hb hab
          simp only [clo,chi,crank,ha,hb,↓reduceIte]
          omega

theorem chained_adj (hk : 0 < k) {x y : BaseVertex K N} (h : (base K N).Adj x y) :
    clo k x ≤ chi k y ∧ clo k y ≤ chi k x := by
  obtain ⟨_,h1 | h1⟩ := (SimpleGraph.fromRel_adj _ _ _).mp h
  · exact chained_rel k hk h1
  · exact (chained_rel k hk h1).symm

/-- A class link is swept at the turn of its reference vertex, an edge link at the
turn of its choice-cycle vertex. -/
def cpos : LinkCode K N → ℕ
  | .inl (s,d) => 2*(2*s.val*cycleLength K N + d.val)
  | .inr (s,_,d) => 2*((2*s.val+1)*cycleLength K N + d.val)

def cslot : LinkCode K N → ℕ
  | .inl _ => 0
  | .inr (_,u,_) => u.val

def linkSlot : LinkCode K N → Fin K
  | .inl (s,_) => s
  | .inr (s,_,_) => s

theorem cslot_lt (l : LinkCode K N) : cslot l < K := by
  rcases l with ⟨s,d⟩ | ⟨s,u,d⟩
  · exact Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
  · exact u.isLt

theorem cpos_bounds (l : LinkCode K N) :
    4*(linkSlot l).val*cycleLength K N ≤ cpos l ∧
    cpos l + 1 ≤ 4*((linkSlot l).val+1)*cycleLength K N ∧ cpos l % 2 = 0 := by
  rcases l with ⟨s,d⟩ | ⟨s,u,d⟩
  · have hd := ZMod.val_lt d
    have e1 : 4*s.val*cycleLength K N = 2*(2*s.val*cycleLength K N) := by ring
    have e2 : 4*(s.val+1)*cycleLength K N = 2*(2*s.val*cycleLength K N) + 4*cycleLength K N := by
      ring
    simp only [cpos,linkSlot]
    omega
  · have hd := ZMod.val_lt d
    have e1 : 4*s.val*cycleLength K N = 2*(2*s.val*cycleLength K N) := by ring
    have e2 : 4*(s.val+1)*cycleLength K N = 2*(2*s.val*cycleLength K N) + 4*cycleLength K N := by
      ring
    have e3 : (2*s.val+1)*cycleLength K N = 2*s.val*cycleLength K N + cycleLength K N := by ring
    simp only [cpos,linkSlot]
    omega

theorem chained_link_inj (l l' : LinkCode K N) (hp : cpos l = cpos l') (hs : cslot l = cslot l') :
    l = l' := by
  rcases l with ⟨s,d⟩ | ⟨s,u,d⟩ <;> rcases l' with ⟨s',d'⟩ | ⟨s',u',d'⟩
  · obtain ⟨h1,h2⟩ := split_mul_add (ZMod.val_lt d) (ZMod.val_lt d')
      (show 2*s.val*cycleLength K N + d.val = 2*s'.val*cycleLength K N + d'.val by
        simp only [cpos] at hp; omega)
    have hss : s = s' := Fin.ext (by omega)
    have hdd : d = d' := ZMod.val_injective _ h2
    rw [hss,hdd]
  · obtain ⟨h1,h2⟩ := split_mul_add (ZMod.val_lt d) (ZMod.val_lt d')
      (show 2*s.val*cycleLength K N + d.val = (2*s'.val+1)*cycleLength K N + d'.val by
        simp only [cpos] at hp; omega)
    omega
  · obtain ⟨h1,h2⟩ := split_mul_add (ZMod.val_lt d) (ZMod.val_lt d')
      (show (2*s.val+1)*cycleLength K N + d.val = 2*s'.val*cycleLength K N + d'.val by
        simp only [cpos] at hp; omega)
    omega
  · obtain ⟨h1,h2⟩ := split_mul_add (ZMod.val_lt d) (ZMod.val_lt d')
      (show (2*s.val+1)*cycleLength K N + d.val = (2*s'.val+1)*cycleLength K N + d'.val by
        simp only [cpos] at hp; omega)
    have hss : s = s' := Fin.ext (by omega)
    have hdd : d = d' := ZMod.val_injective _ h2
    have huu : u = u' := Fin.ext hs
    rw [hss,hdd,huu]

/-- Every position of a link lies in the block of the layer of its slot. -/
theorem cpos_block (hk : 0 < k) (l : LinkCode K N) :
    (linkSlot l).val/k*layerSpan k K N ≤ cpos l ∧
    cpos l + 1 ≤ ((linkSlot l).val/k+1)*layerSpan k K N := by
  obtain ⟨h1,h2,_⟩ := cpos_bounds l
  obtain ⟨b1,b2⟩ := block_bounds (N := N) k hk (linkSlot l)
  omega

theorem cpos_le (hk : 0 < k) (l : LinkCode K N) : cpos l ≤ chainedP k K N := by
  have h1 := (cpos_block k hk l).2
  have h2 := block_le_P (N := N) k (linkSlot l)
  omega

theorem chained_src (hk : 0 < k) (l : LinkCode K N) :
    clo k (src l) ≤ cpos l ∧ cpos l ≤ chi k (src l) := by
  have hP := cpos_le k hk l
  have hblock := cpos_block k hk l
  rcases l with ⟨s,d⟩ | ⟨s,u,d⟩
  · change clo k (.inl (ref s d)) ≤ _ ∧ _ ≤ chi k (.inl (ref s d))
    rcases hr : ref s d with a | ⟨s',e⟩
    · exact ⟨Nat.zero_le _,hP⟩
    · obtain ⟨hs,hd⟩ := ref_private hr
      subst hs
      simp only [clo,chi,crank,cpos]
      omega
  · change clo k (.inr (s,d)) ≤ _ ∧ _ ≤ chi k (.inr (s,d))
    by_cases hd : d = 0
    · subst hd
      exact hub_present k hk s _ _ (Or.inl rfl) hblock.1 hblock.2
    · simp only [clo,chi,crank,cpos,hd,↓reduceIte]
      omega

theorem chained_dst (hk : 0 < k) (l : Link k Γ) :
    clo k (dst l.val) ≤ cpos l.val ∧ cpos l.val ≤ chi k (dst l.val) := by
  have hblock := cpos_block k hk l.val
  rcases l with ⟨(⟨s,d⟩ | ⟨s,u,d⟩),hv⟩
  · exact hub_present k hk s _ _ (Or.inl rfl) hblock.1 hblock.2
  · obtain ⟨⟨hsu,hreq⟩,_⟩ := hv
    have h1 : s.val / k ≤ u.val / k := Nat.div_le_div_right (Nat.le_of_lt hsu)
    have h2 : u.val / k ≤ s.val / k + 1 := hreq
    exact hub_present k hk u _ (s.val/k) (by omega) hblock.1 hblock.2

theorem crank_inj {x y : BaseVertex K N} (hx : ¬ bret x) (hy : ¬ bret y)
    (h : crank x = crank y) : x = y := by
  rcases x with (a | ⟨s,e⟩) | ⟨s,a⟩
  · exact absurd trivial hx
  · have he := e.isLt
    rcases y with (b | ⟨s',e'⟩) | ⟨s',a'⟩
    · exact absurd trivial hy
    · have he' := e'.isLt
      obtain ⟨h1,h2⟩ := split_mul_add (n := cycleLength K N) (by omega : e.val+2 < _)
        (by omega : e'.val+2 < _) h
      have hss : s = s' := Fin.ext (by omega)
      have hee : e = e' := Fin.ext (by omega)
      rw [hss,hee]
    · obtain ⟨h1,h2⟩ := split_mul_add (n := cycleLength K N) (by omega : e.val+2 < _)
        (ZMod.val_lt a') h
      omega
  · rcases y with (b | ⟨s',e'⟩) | ⟨s',a'⟩
    · exact absurd trivial hy
    · have he' := e'.isLt
      obtain ⟨h1,h2⟩ := split_mul_add (n := cycleLength K N) (ZMod.val_lt a)
        (by omega : e'.val+2 < _) h
      omega
    · obtain ⟨h1,h2⟩ := split_mul_add (n := cycleLength K N) (ZMod.val_lt a) (ZMod.val_lt a') h
      have hss : s = s' := Fin.ext (by omega)
      have haa : a = a' := ZMod.val_injective _ h2
      rw [hss,haa]

/-- At most two shared vertices, `2k` hubs and two other vertices are present at a
position; at an even position at most one other vertex. -/
theorem chained_count (hk : 0 < k) (p : ℕ) :
    (Finset.univ.filter (fun x : BaseVertex K N => clo k x ≤ p ∧ p ≤ chi k x)).card ≤ 2*k+4 ∧
    (p % 2 = 0 →
      (Finset.univ.filter (fun x : BaseVertex K N => clo k x ≤ p ∧ p ≤ chi k x)).card ≤ 2*k+3) := by
  have hW := layerSpan_pos (K := K) (N := N) k hk
  obtain ⟨lam,hlam⟩ : ∃ lam, lam = p / layerSpan k K N := ⟨_,rfl⟩
  let shared : Finset (BaseVertex K N) :=
    (Finset.univ : Finset (Fin 2)).map ⟨fun a => .inl (.inl a),fun a b h => Sum.inl.inj (Sum.inl.inj h)⟩
  let hubs : Finset (BaseVertex K N) :=
    ((Finset.univ.filter (fun s : Fin K => s.val / k = lam)) ∪
      (Finset.univ.filter (fun s : Fin K => s.val / k = lam + 1))).map
      ⟨fun s => .inr (s,0),fun a b h => congrArg Prod.fst (Sum.inr.inj h)⟩
  let moving : Finset (BaseVertex K N) :=
    Finset.univ.filter (fun x => ¬ bret x ∧ 2*crank x - 1 ≤ p ∧ p ≤ 2*crank x + 1)
  have hsub : Finset.univ.filter (fun x : BaseVertex K N => clo k x ≤ p ∧ p ≤ chi k x) ⊆
      shared ∪ hubs ∪ moving := by
    intro x hx
    have hx' : clo k x ≤ p ∧ p ≤ chi k x := (Finset.mem_filter.mp hx).2
    by_cases hr : bret x
    · apply Finset.mem_union_left
      rcases x with (a | ⟨s,e⟩) | ⟨s,a⟩
      · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨a,Finset.mem_univ _,rfl⟩)
      · exact absurd hr id
      · have ha : a = 0 := hr
        subst ha
        apply Finset.mem_union_right
        refine Finset.mem_map.mpr ⟨s,?_,rfl⟩
        simp only [clo,chi,↓reduceIte] at hx'
        have h1 : s.val/k - 1 ≤ lam := by
          rw [hlam]
          exact (Nat.le_div_iff_mul_le hW).mpr hx'.1
        have hpos : 0 < (s.val/k+1)*layerSpan k K N := Nat.mul_pos (Nat.succ_pos _) hW
        have h2 : lam < s.val/k + 1 := by
          rw [hlam]
          exact (Nat.div_lt_iff_lt_mul hW).mpr
            (Nat.lt_of_le_of_lt hx'.2 (Nat.sub_lt hpos Nat.one_pos))
        simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
        omega
    · obtain ⟨l1,l2⟩ := ranked_lo_hi k x hr
      rw [l1,l2] at hx'
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr,hx'⟩)
  have hshared : shared.card ≤ 2 := by simp [shared]
  have hhubs : hubs.card ≤ 2*k := by
    have h1 := layer_card (K := K) k hk lam
    have h2 := layer_card (K := K) k hk (lam+1)
    have h3 := Finset.card_union_le (Finset.univ.filter (fun s : Fin K => s.val / k = lam))
      (Finset.univ.filter (fun s : Fin K => s.val / k = lam + 1))
    simp only [hubs,Finset.card_map]
    omega
  have hmoving : ∀ E : Finset ℕ, (∀ x ∈ moving, crank x ∈ E) → moving.card ≤ E.card :=
    fun E hE => card_le_of_rank moving crank E hE
      (fun x hx y hy h => crank_inj (Finset.mem_filter.mp hx).2.1 (Finset.mem_filter.mp hy).2.1 h)
  have hc := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  constructor
  · have h2 : moving.card ≤ 2 := by
      refine (hmoving {p/2,(p+1)/2} ?_).trans Finset.card_le_two
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2.2
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
    omega
  · intro hp
    have h1 : moving.card ≤ 1 := by
      refine (hmoving {p/2} ?_).trans (by simp)
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2.2
      simp only [Finset.mem_singleton]
      omega
    omega

/-- The source of the chained reduction has pathwidth at most `2k+4`, whatever the
number of layers. -/
theorem source_pathWidth (hk : 0 < k) : HasPathWidth (source k Γ) (2*k+4) := by
  have h5 := five_le_cycleLength K N
  refine hasPathWidth_linked (base K N) (fun l : Link k Γ => src l.val) (fun l => dst l.val)
    (cycleLength K N - 3) (by omega) (chainedP k K N) K (2*k+4) (clo k) (chi k)
    (clo_le_chi k hk) (chi_le k hk) (fun x y h => chained_adj k hk h)
    (fun l => cpos l.val) (fun l => cslot l.val) (fun l => cslot_lt l.val)
    (fun l l' hp hs => Subtype.ext (chained_link_inj l.val l'.val hp hs))
    (fun l => chained_src k hk l.val) (fun l => chained_dst k Γ hk l)
    (fun p => by have := (chained_count (K := K) (N := N) k hk p).1; omega)
    (fun l => by
      have := (chained_count (K := K) (N := N) k hk (cpos l.val)).2 (cpos_bounds l.val).2.2
      omega)

end ChainedPath
end Chained

/-! ## Main theorems with pathwidth -/

/-- The plain reduction, with path-decomposition certificates: source pathwidth at
most `k+3` and target pathwidth at most two. -/
theorem reduction_pathWidth {k N : ℕ} (Γ : SimpleGraph (Fin k × Fin N)) :
    (Nonempty (source Γ →g cycleGraph (cycleLength k N)) ↔ MulticolouredClique Γ) ∧
    HasPathWidth (source Γ) (k+3) ∧ HasPathWidth (cycleGraph (cycleLength k N)) 2 := by
  have h1 := source_hom_iff_clique Γ
  have h2 := target_pathWidth (cycleLength k N) (by have := five_le_cycleLength k N; omega)
  rw [target_eq_cycleGraph] at h1 h2
  exact ⟨h1,source_pathWidth Γ,h2⟩

/-- The chained reduction, with path-decomposition certificates: source pathwidth at
most `2k+4`, independently of the number of slots, and target pathwidth at most two. -/
theorem Chained.reduction_pathWidth {K N : ℕ} (k : ℕ) (hk : 0 < k)
    (Γ : SimpleGraph (Fin K × Fin N)) :
    (Nonempty (Chained.source k Γ →g cycleGraph (cycleLength K N)) ↔ Chained.ChainedClique k Γ) ∧
    HasPathWidth (Chained.source k Γ) (2*k+4) ∧
    HasPathWidth (cycleGraph (cycleLength K N)) 2 := by
  have h1 := Chained.source_hom_iff_clique k Γ
  have h2 := target_pathWidth (cycleLength K N) (by have := five_le_cycleLength K N; omega)
  rw [target_eq_cycleGraph] at h1 h2
  exact ⟨h1,Chained.source_pathWidth k Γ hk,h2⟩

end TreewidthHom.OddCycle
