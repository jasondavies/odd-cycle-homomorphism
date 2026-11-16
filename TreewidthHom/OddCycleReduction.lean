module

public import TreewidthHom.OddCycleTarget
public import TreewidthHom.Links
public import TreewidthHom.ApexForest

@[expose] public section

/-!
# Multicoloured Clique reduces to homomorphism into an odd cycle

The source consists of `k+1` dials (copies of the target cycle) and paths of
length `n-2` forcing chosen pairs of dial vertices apart. See `ODD_CYCLE.md`.
-/
namespace TreewidthHom.OddCycle
open SimpleGraph

variable {k N : ℕ}

/-- A clique with exactly one vertex in each of the `k` classes of size `N`. -/
def MulticolouredClique (Γ : SimpleGraph (Fin k × Fin N)) : Prop :=
  ∃ c : Fin k → Fin N, ∀ i j, i < j → Γ.Adj (i,c i) (j,c j)

/-! ## Labels -/

def weight (k N : ℕ) (i : Fin k) : ℕ := 2*N*k+1+i.val
def label (i : Fin k) (a : Fin N) : ℕ := (a.val+1)*weight k N i
def halfLength (k N : ℕ) : ℕ := N*(2*N*k+1+k)+2
def cycleLength (k N : ℕ) : ℕ := 2*halfLength k N+1

theorem cycleLength_odd (k N : ℕ) : Odd (cycleLength k N) := ⟨halfLength k N,rfl⟩

theorem five_le_cycleLength (k N : ℕ) : 5 ≤ cycleLength k N := by
  unfold cycleLength halfLength
  omega

instance (k N : ℕ) : Fact (1 < cycleLength k N) :=
  ⟨by have := five_le_cycleLength k N; omega⟩

instance (k N : ℕ) : NeZero (cycleLength k N) :=
  ⟨by have := five_le_cycleLength k N; omega⟩

theorem label_pos (i : Fin k) (a : Fin N) : 1 ≤ label i a := by
  unfold label weight
  exact Nat.mul_pos (by omega) (by omega)

theorem label_le (i : Fin k) (a : Fin N) : label i a + 2 ≤ halfLength k N := by
  unfold label weight halfLength
  have h1 : a.val+1 ≤ N := a.isLt
  have h2 : 2*N*k+1+i.val ≤ 2*N*k+1+k := by have := i.isLt; omega
  have := Nat.mul_le_mul h1 h2
  omega

/-! ## Arithmetic of label differences -/

theorem diff_zero {Q i j x y : ℤ} (hij : i ≠ j) (h : x*(Q+j) = y*(Q+i))
    (hb : |y*i - x*j| < Q) : x = 0 ∧ y = 0 := by
  have hQ : 0 < Q := lt_of_le_of_lt (abs_nonneg _) hb
  have h1 : (x - y)*Q = y*i - x*j := by linear_combination h
  have hxy : x = y := by
    by_contra hne
    have h2 : 1 ≤ |x - y| := Int.one_le_abs (sub_ne_zero.mpr hne)
    have h3 : |x - y| * Q = |y*i - x*j| := by rw [← h1,abs_mul,abs_of_pos hQ]
    have h4 := mul_le_mul_of_nonneg_right h2 hQ.le
    linarith
  subst hxy
  have h4 : x*(j - i) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact ⟨h5,h5⟩
  · exact absurd (sub_eq_zero.mp h5).symm hij

theorem int_eq_of_cast {n : ℕ} {X Y : ℤ} (h : (X : ZMod n) = (Y : ZMod n))
    (hb : |Y - X| < n) : X = Y := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub X Y n).mp h
  have := Int.eq_zero_of_abs_lt_dvd hd hb
  linarith

theorem abs_mul_le {y i A B : ℤ} (hy : |y| ≤ A) (hi : 0 ≤ i) (hiB : i ≤ B) : |y*i| ≤ A*B := by
  rw [abs_mul,abs_of_nonneg hi]
  exact mul_le_mul hy hiB hi (le_trans (abs_nonneg y) hy)

/-- A label difference between two classes determines both vertices, and is
never the negative of another such difference. -/
theorem label_solve (i j : Fin k) (hij : i < j) (a a' b b' : Fin N)
    (δ : ZMod (cycleLength k N)) (hδ : δ = 1 ∨ δ = -1)
    (h : δ * ((label j b' : ZMod (cycleLength k N)) - label i a') =
      (label j b : ZMod (cycleLength k N)) - label i a) : a' = a ∧ b' = b := by
  have hn : cycleLength k N = 2*halfLength k N+1 := rfl
  have la := label_le i a; have la' := label_le i a'
  have lb := label_le j b; have lb' := label_le j b'
  have pa := label_pos i a; have pa' := label_pos i a'
  have pb := label_pos j b; have pb' := label_pos j b'
  have hi : (i.val : ℤ) < k := by exact_mod_cast i.isLt
  have hj : (j.val : ℤ) < k := by exact_mod_cast j.isLt
  have hne : (i.val : ℤ) ≠ j.val := by
    have : i.val < j.val := hij
    omega
  have hN : (0 : ℤ) ≤ N := by positivity
  have ea : (label i a : ℤ) = ((a.val : ℤ)+1)*((2*N*k+1)+i.val) := by
    unfold label weight; push_cast; ring
  have ea' : (label i a' : ℤ) = ((a'.val : ℤ)+1)*((2*N*k+1)+i.val) := by
    unfold label weight; push_cast; ring
  have eb : (label j b : ℤ) = ((b.val : ℤ)+1)*((2*N*k+1)+j.val) := by
    unfold label weight; push_cast; ring
  have eb' : (label j b' : ℤ) = ((b'.val : ℤ)+1)*((2*N*k+1)+j.val) := by
    unfold label weight; push_cast; ring
  have va : (a.val : ℤ) < N := by exact_mod_cast a.isLt
  have va' : (a'.val : ℤ) < N := by exact_mod_cast a'.isLt
  have vb : (b.val : ℤ) < N := by exact_mod_cast b.isLt
  have vb' : (b'.val : ℤ) < N := by exact_mod_cast b'.isLt
  rcases hδ with rfl | rfl
  · rw [one_mul] at h
    have hc : (((label j b' : ℤ) - label i a' : ℤ) : ZMod (cycleLength k N)) =
        (((label j b : ℤ) - label i a : ℤ) : ZMod (cycleLength k N)) := by
      push_cast; exact h
    have hint := int_eq_of_cast hc (by rw [abs_lt]; constructor <;> omega)
    rw [ea,ea',eb,eb'] at hint
    have hz := diff_zero (Q := 2*N*k+1) (i := i.val) (j := j.val)
      (x := (b'.val : ℤ) - b.val) (y := (a'.val : ℤ) - a.val) hne
      (by linear_combination hint) (by
        have h1 := abs_mul_le (y := (a'.val : ℤ) - a.val) (i := i.val) (A := N) (B := k)
          (by rw [abs_le]; constructor <;> omega) (by positivity) hi.le
        have h2 := abs_mul_le (y := (b'.val : ℤ) - b.val) (i := j.val) (A := N) (B := k)
          (by rw [abs_le]; constructor <;> omega) (by positivity) hj.le
        have h3 := abs_sub (((a'.val : ℤ) - a.val)*i.val) (((b'.val : ℤ) - b.val)*j.val)
        linarith)
    exact ⟨Fin.ext (by omega),Fin.ext (by omega)⟩
  · rw [neg_one_mul] at h
    have hc : ((-((label j b' : ℤ) - label i a') : ℤ) : ZMod (cycleLength k N)) =
        (((label j b : ℤ) - label i a : ℤ) : ZMod (cycleLength k N)) := by
      push_cast; exact h
    have hint := int_eq_of_cast hc (by rw [abs_lt]; constructor <;> omega)
    rw [ea,ea',eb,eb'] at hint
    have hz := diff_zero (Q := 2*N*k+1) (i := i.val) (j := j.val)
      (x := (b'.val : ℤ) + b.val + 2) (y := (a'.val : ℤ) + a.val + 2) hne
      (by linear_combination -hint) (by
        have hk : (0 : ℤ) ≤ k := by positivity
        have h1 : (0 : ℤ) ≤ ((a'.val : ℤ) + a.val + 2)*i.val := by positivity
        have h2 : (0 : ℤ) ≤ ((b'.val : ℤ) + b.val + 2)*j.val := by positivity
        have h3 : ((a'.val : ℤ) + a.val + 2)*i.val ≤ (2*N)*k :=
          mul_le_mul (by omega) hi.le (by positivity) (by positivity)
        have h4 : ((b'.val : ℤ) + b.val + 2)*j.val ≤ (2*N)*k :=
          mul_le_mul (by omega) hj.le (by positivity) (by positivity)
        rw [abs_lt]
        constructor <;> linarith)
    have : (0 : ℤ) ≤ b'.val := by positivity
    have : (0 : ℤ) ≤ b.val := by positivity
    omega

/-! ## The source graph -/

abbrev DialVertex (k N : ℕ) := Fin (k+1) × ZMod (cycleLength k N)

/-- `k+1` disjoint copies of the target cycle. -/
def dials (k N : ℕ) : SimpleGraph (DialVertex k N) where
  Adj x y := x.1 = y.1 ∧ (cyc (cycleLength k N)).Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => (cyc _).loopless.irrefl _ h.2⟩

abbrev LinkCode (k N : ℕ) :=
  (Fin k × ZMod (cycleLength k N)) ⊕ (Fin k × Fin k × ZMod (cycleLength k N))

/-- Class links forbid values that label no vertex of the class. Edge links forbid
differences that come from no edge between the two classes. -/
def Valid (Γ : SimpleGraph (Fin k × Fin N)) : LinkCode k N → Prop
  | .inl (i,d) => ∀ a : Fin N, d ≠ (label i a : ZMod (cycleLength k N))
  | .inr (i,j,d) => i < j ∧ ∀ a b : Fin N, Γ.Adj (i,a) (j,b) →
      d ≠ (label j b : ZMod (cycleLength k N)) - (label i a : ZMod (cycleLength k N))

def src : LinkCode k N → DialVertex k N
  | .inl (_,d) => (0,d)
  | .inr (i,_,d) => (i.succ,d)

/-- Every link ends at the hub of a dial. -/
def dst : LinkCode k N → DialVertex k N
  | .inl (i,_) => (i.succ,0)
  | .inr (_,j,_) => (j.succ,0)

theorem dst_snd (c : LinkCode k N) : (dst c).2 = 0 := by
  rcases c with ⟨i,d⟩ | ⟨i,j,d⟩ <;> rfl

abbrev Link (Γ : SimpleGraph (Fin k × Fin N)) := {c : LinkCode k N // Valid Γ c}

abbrev SourceVertex (Γ : SimpleGraph (Fin k × Fin N)) :=
  DialVertex k N ⊕ (Link Γ × Fin (cycleLength k N - 3))

/-- The dials, with a path of length `n-2` for every link. -/
def source (Γ : SimpleGraph (Fin k × Fin N)) : SimpleGraph (SourceVertex Γ) :=
  linked (dials k N) (fun l : Link Γ => src l.val) (fun l => dst l.val) (cycleLength k N - 3)

/-! ## Correctness -/

theorem source_hom_iff (Γ : SimpleGraph (Fin k × Fin N)) :
    Nonempty (source Γ →g cyc (cycleLength k N)) ↔
      ∃ φ : dials k N →g cyc (cycleLength k N), ∀ l : Link Γ, φ (src l.val) ≠ φ (dst l.val) := by
  have h5 := five_le_cycleLength k N
  have hq : cycleLength k N - 3 + 1 = cycleLength k N - 2 := by omega
  unfold source
  rw [linked_hom_iff _ _ _ _ (by omega)]
  constructor
  · rintro ⟨φ,h⟩
    refine ⟨φ,fun l => ?_⟩
    obtain ⟨w,h0,h1,hs⟩ := h l
    rw [hq] at h1
    exact (walk_iff_ne (cycleLength_odd k N) (by omega) _ _).mp
      ⟨w,h0,h1,fun t ht => (cyc_adj _ _).mp (hs t (by omega))⟩
  · rintro ⟨φ,h⟩
    refine ⟨φ,fun l => ?_⟩
    obtain ⟨w,h0,h1,hs⟩ := (walk_iff_ne (cycleLength_odd k N) (by omega) _ _).mpr (h l)
    refine ⟨w,h0,?_,fun i hi => (cyc_adj _ _).mpr (hs i (by omega))⟩
    rw [hq]
    exact h1

/-- Rotation of each dial by the label of the chosen vertex of its class. -/
def shift (c : Fin k → Fin N) : Fin (k+1) → ZMod (cycleLength k N) :=
  Fin.cases 0 (fun i => (label i (c i) : ZMod (cycleLength k N)))

theorem hom_of_clique (Γ : SimpleGraph (Fin k × Fin N)) (h : MulticolouredClique Γ) :
    Nonempty (source Γ →g cyc (cycleLength k N)) := by
  obtain ⟨c,hc⟩ := h
  rw [source_hom_iff]
  refine ⟨⟨fun x => shift c x.1 + x.2,?_⟩,?_⟩
  · rintro ⟨i,a⟩ ⟨j,b⟩ ⟨hij,hab⟩
    dsimp only at hij
    subst hij
    exact (cyc_adj _ _).mpr (((cyc_adj _ _).mp hab).add_left _)
  · rintro ⟨(⟨i,d⟩ | ⟨i,j,d⟩),hv⟩
    · have hv' := hv (c i)
      change shift c 0 + d ≠ shift c i.succ + 0
      simpa [shift] using hv'
    · obtain ⟨hij,hv'⟩ := hv
      change shift c i.succ + d ≠ shift c j.succ + 0
      simp only [shift,Fin.cases_succ,add_zero]
      intro he
      exact hv' (c i) (c j) (hc i j hij) (by rw [← he]; ring)

theorem clique_of_hom (Γ : SimpleGraph (Fin k × Fin N))
    (h : Nonempty (source Γ →g cyc (cycleLength k N))) : MulticolouredClique Γ := by
  rw [source_hom_iff] at h
  obtain ⟨φ,hlink⟩ := h
  have hdial : ∀ i : Fin (k+1), ∃ r ε : ZMod (cycleLength k N), (ε = 1 ∨ ε = -1) ∧
      ∀ x, φ (i,x) = r + ε*x := by
    intro i
    apply dial (cycleLength_odd k N) (fun a => φ (i,a))
    intro x
    apply (cyc_adj _ _).mp
    exact φ.map_rel ⟨rfl,(cyc_adj _ _).mpr (Or.inl rfl)⟩
  choose r ε hε hf using hdial
  have hsq : ∀ i, ε i * ε i = 1 := by
    intro i
    rcases hε i with h | h <;> rw [h] <;> ring
  have hclass : ∀ i : Fin k, ∃ a : Fin N,
      ε 0 * (r i.succ - r 0) = (label i a : ZMod (cycleLength k N)) := by
    intro i
    by_contra hno
    push Not at hno
    have hl := hlink ⟨.inl (i,ε 0 * (r i.succ - r 0)),hno⟩
    apply hl
    change φ (0,_) = φ (i.succ,0)
    rw [hf,hf]
    linear_combination (r i.succ - r 0) * hsq 0
  choose a ha using hclass
  refine ⟨a,fun i j hij => ?_⟩
  have hedge : ∃ a' b' : Fin N, Γ.Adj (i,a') (j,b') ∧
      ε i.succ * (r j.succ - r i.succ) =
        (label j b' : ZMod (cycleLength k N)) - (label i a' : ZMod (cycleLength k N)) := by
    by_contra hno
    push Not at hno
    have hl := hlink ⟨.inr (i,j,ε i.succ * (r j.succ - r i.succ)),hij,hno⟩
    apply hl
    change φ (i.succ,_) = φ (j.succ,0)
    rw [hf,hf]
    linear_combination (r j.succ - r i.succ) * hsq i.succ
  obtain ⟨a',b',hadj,heq⟩ := hedge
  have hr : r j.succ - r i.succ =
      ε 0 * ((label j (a j) : ZMod (cycleLength k N)) - label i (a i)) := by
    linear_combination ε 0 * (ha j - ha i) - (r j.succ - r i.succ) * hsq 0
  rw [hr,← mul_assoc] at heq
  have hδ : ε i.succ * ε 0 = 1 ∨ ε i.succ * ε 0 = -1 := by
    rcases hε i.succ with h1 | h1 <;> rcases hε 0 with h2 | h2 <;> rw [h1,h2] <;> simp
  obtain ⟨h1,h2⟩ := label_solve i j hij a' (a i) b' (a j) _ hδ heq
  rw [h1,h2]
  exact hadj

/-- Decision equivalence of the reduction. -/
theorem source_hom_iff_clique (Γ : SimpleGraph (Fin k × Fin N)) :
    Nonempty (source Γ →g cyc (cycleLength k N)) ↔ MulticolouredClique Γ :=
  ⟨clique_of_hom Γ,hom_of_clique Γ⟩

/-! ## Width -/

section Pred
variable {n : ℕ} [Fact (1 < n)]

theorem sub_one_ne_zero {a : ZMod n} (h : 1 < a.val) : a - 1 ≠ 0 := by
  intro h0
  have h1 : a = 1 := sub_eq_zero.mp h0
  rw [h1,ZMod.val_one] at h
  omega

theorem val_sub_one {a : ZMod n} (h : 1 ≤ a.val) : (a - 1).val + 1 = a.val := by
  have hn : NeZero n := ⟨by have := Fact.out (p := 1 < n); omega⟩
  rw [ZMod.val_sub (by rw [ZMod.val_one]; exact h),ZMod.val_one]
  omega

theorem one_lt_val_of_succ {a b : ZMod n} (ha : a ≠ 0) (hb : b ≠ 0) (h : b = a + 1) :
    1 < b.val := by
  have hn : NeZero n := ⟨by have := Fact.out (p := 1 < n); omega⟩
  have h0 : b.val ≠ 0 := fun h0 => hb ((ZMod.val_eq_zero b).mp h0)
  have h1 : b.val ≠ 1 := by
    intro h1
    have hb1 : b = 1 := by
      apply ZMod.val_injective n
      rw [h1,ZMod.val_one]
    rw [hb1] at h
    exact ha (by linear_combination -h)
  omega

/-- A cycle is a path plus one hub. -/
theorem target_width (n : ℕ) [Fact (1 < n)] : HasWidth (cyc n) 2 := by
  classical
  have h := hasWidth_of_apex_forest (cyc n) (fun a => a = 0)
    (fun p => if h : 1 < p.val.val then some ⟨p.val - 1,sub_one_ne_zero h⟩ else none)
    (fun p => p.val.val)
    (by
      intro p q hpq
      by_cases hp : 1 < p.val.val
      · rw [dite_eq_left hp] at hpq
        have hq := Option.some.inj hpq
        rw [← hq]
        have := val_sub_one (a := p.val) (by omega)
        dsimp only
        omega
      · rw [dite_eq_right hp] at hpq
        cases hpq)
    (by
      rintro ⟨a,ha⟩ ⟨b,hb⟩ hadj
      have hadj' : (cyc n).Adj a b := hadj
      rcases (cyc_adj _ _).mp hadj' with h | h
      · right
        have hb2 := one_lt_val_of_succ ha hb h
        have he : b - 1 = a := by rw [h]; ring
        simp [hb2,he]
      · left
        have ha2 := one_lt_val_of_succ hb ha h
        have he : a - 1 = b := by rw [h]; ring
        simp [ha2,he])
  simpa using h

end Pred

section SourceWidth
variable (Γ : SimpleGraph (Fin k × Fin N))

/-- The vertex 0 of every dial. Deleting these `k+1` vertices leaves a forest. -/
def hub : SourceVertex Γ → Prop
  | .inl x => x.2 = 0
  | .inr _ => False

def hubEquiv : Fin (k+1) ≃ {v : SourceVertex Γ // hub Γ v} where
  toFun i := ⟨.inl (i,0),rfl⟩
  invFun v := match v with
    | ⟨.inl x,_⟩ => x.1
    | ⟨.inr _,h⟩ => h.elim
  left_inv := fun _ => rfl
  right_inv := by
    rintro ⟨(⟨i,a⟩ | x),h⟩
    · have ha : a = 0 := h
      subst ha
      rfl
    · exact h.elim

noncomputable instance hubFintype : Fintype {v : SourceVertex Γ // hub Γ v} :=
  Fintype.ofEquiv _ (hubEquiv Γ)

theorem hub_card : Fintype.card {v : SourceVertex Γ // hub Γ v} = k+1 := by
  rw [Fintype.card_congr (hubEquiv Γ).symm,Fintype.card_fin]

/-- Parent pointers: down each dial towards its hub, and down each link towards
the dial vertex it hangs from. -/
def par : SourceVertex Γ → Option (SourceVertex Γ)
  | .inl (i,a) => if 1 < a.val then some (.inl (i,a-1)) else none
  | .inr (l,c) =>
      if hc : c.val = 0 then (if (src l.val).2 = 0 then none else some (.inl (src l.val)))
      else some (.inr (l,⟨c.val-1,by omega⟩))

def ht : SourceVertex Γ → ℕ
  | .inl (_,a) => a.val
  | .inr (_,c) => cycleLength k N + c.val

theorem par_not_hub {v w : SourceVertex Γ} (h : par Γ v = some w) : ¬ hub Γ w := by
  rcases v with ⟨i,a⟩ | ⟨l,c⟩
  · by_cases ha : 1 < a.val
    · have hw : w = .inl (i,a-1) := by simpa [par,ha] using h.symm
      subst hw
      exact sub_one_ne_zero ha
    · simp [par,ha] at h
  · by_cases hc : c.val = 0
    · by_cases hs : (src l.val).2 = 0
      · simp [par,hc,hs] at h
      · have hw : w = .inl (src l.val) := by simpa [par,hc,hs] using h.symm
        subst hw
        exact hs
    · have hw : w = .inr (l,⟨c.val-1,by omega⟩) := by simpa [par,hc] using h.symm
      subst hw
      exact id

theorem par_ht {v w : SourceVertex Γ} (h : par Γ v = some w) : ht Γ w < ht Γ v := by
  rcases v with ⟨i,a⟩ | ⟨l,c⟩
  · by_cases ha : 1 < a.val
    · have hw : w = .inl (i,a-1) := by simpa [par,ha] using h.symm
      subst hw
      have := val_sub_one (a := a) (by omega)
      change (a-1).val < a.val
      omega
    · simp [par,ha] at h
  · by_cases hc : c.val = 0
    · by_cases hs : (src l.val).2 = 0
      · simp [par,hc,hs] at h
      · have hw : w = .inl (src l.val) := by simpa [par,hc,hs] using h.symm
        subst hw
        have := ZMod.val_lt (src l.val).2
        change (src l.val).2.val < cycleLength k N + c.val
        omega
    · have hw : w = .inr (l,⟨c.val-1,by omega⟩) := by simpa [par,hc] using h.symm
      subst hw
      change cycleLength k N + (c.val-1) < cycleLength k N + c.val
      omega

/-- Every edge between two vertices that are not hubs is a parent pointer. -/
theorem par_edge {v w : SourceVertex Γ} (hv : ¬ hub Γ v) (hw : ¬ hub Γ w)
    (h : (source Γ).Adj v w) : par Γ v = some w ∨ par Γ w = some v := by
  rcases v with ⟨i,a⟩ | ⟨l,c⟩ <;> rcases w with ⟨j,b⟩ | ⟨l',c'⟩
  · obtain ⟨hij,hab⟩ : i = j ∧ (cyc (cycleLength k N)).Adj a b := h
    subst hij
    have ha : a ≠ 0 := hv
    have hb : b ≠ 0 := hw
    rcases (cyc_adj _ _).mp hab with h1 | h1
    · right
      have hb2 := one_lt_val_of_succ ha hb h1
      have he : b - 1 = a := by rw [h1]; ring
      simp [par,hb2,he]
    · left
      have ha2 := one_lt_val_of_succ hb ha h1
      have he : a - 1 = b := by rw [h1]; ring
      simp [par,ha2,he]
  · have h' : (c'.val = 0 ∧ (i,a) = src l'.val) ∨
        (c'.val+1 = cycleLength k N - 3 ∧ (i,a) = dst l'.val) := h
    rcases h' with ⟨hc,hs⟩ | ⟨_,hd⟩
    · right
      have hne : ¬ (src l'.val).2 = 0 := by rw [← hs]; exact hv
      simp [par,hc,hne,hs]
    · exact absurd (by rw [hd]; exact dst_snd _) hv
  · have h' : (c.val = 0 ∧ (j,b) = src l.val) ∨
        (c.val+1 = cycleLength k N - 3 ∧ (j,b) = dst l.val) := h
    rcases h' with ⟨hc,hs⟩ | ⟨_,hd⟩
    · left
      have hne : ¬ (src l.val).2 = 0 := by rw [← hs]; exact hw
      simp [par,hc,hne,hs]
    · exact absurd (by rw [hd]; exact dst_snd _) hw
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

def parent (p : {v : SourceVertex Γ // ¬ hub Γ v}) : Option {v : SourceVertex Γ // ¬ hub Γ v} :=
  match h : par Γ p.val with
  | none => none
  | some w => some ⟨w,par_not_hub Γ h⟩

theorem parent_eq_some (p q : {v : SourceVertex Γ // ¬ hub Γ v}) :
    parent Γ p = some q ↔ par Γ p.val = some q.val := by
  unfold parent
  split
  · rename_i h
    simp [h]
  · rename_i w h
    simp [h,Subtype.ext_iff]

/-- The source has a feedback vertex set of `k+1` vertices, hence width at most `k+2`. -/
theorem source_width : HasWidth (source Γ) (k+2) := by
  have h := hasWidth_of_apex_forest (source Γ) (hub Γ) (parent Γ) (fun p => ht Γ p.val)
    (fun p q hpq => par_ht Γ ((parent_eq_some Γ p q).mp hpq))
    (fun p q hadj => (par_edge Γ p.prop q.prop hadj).imp
      (parent_eq_some Γ p q).mpr (parent_eq_some Γ q p).mpr)
  rwa [hub_card] at h

/-- The `k+1` hubs form a feedback vertex set of the source. -/
theorem source_feedback :
    Fintype.card {v : SourceVertex Γ // hub Γ v} = k+1 ∧
    ((source Γ).induce {v | ¬ hub Γ v}).IsAcyclic :=
  ⟨hub_card Γ,acyclic_of_apex_forest (source Γ) (hub Γ) (parent Γ) (fun p => ht Γ p.val)
    (fun p q hpq => par_ht Γ ((parent_eq_some Γ p q).mp hpq))
    (fun p q hadj => (par_edge Γ p.prop q.prop hadj).imp
      (parent_eq_some Γ p q).mpr (parent_eq_some Γ q p).mpr)⟩

/-! ## Size -/

noncomputable instance linkFintype : Fintype (Link Γ) := by
  classical exact Subtype.fintype _

theorem size_arith (k n L : ℕ) (h5 : 5 ≤ n) (hL : L ≤ k*n + k*(k*n)) :
    (k+1)*n + L*(n-3) ≤ (k+1)^2*n^2 := by
  have h1 : L*(n-3) ≤ (k*n+k*(k*n))*n := Nat.mul_le_mul hL (by omega)
  have h2 : (k+1)*n ≤ (k+1)*n*n := Nat.le_mul_of_pos_right _ (by omega)
  calc (k+1)*n + L*(n-3) ≤ (k+1)*n*n + (k*n+k*(k*n))*n := Nat.add_le_add h2 h1
    _ = (k+1)^2*n^2 := by ring

theorem source_card_le :
    Fintype.card (SourceVertex Γ) ≤ (k+1)^2*(cycleLength k N)^2 := by
  have hL : Fintype.card (Link Γ) ≤ Fintype.card (LinkCode k N) := Fintype.card_subtype_le _
  have hC : Fintype.card (LinkCode k N) = k*cycleLength k N + k*(k*cycleLength k N) := by
    simp [LinkCode,ZMod.card]
  have hV : Fintype.card (SourceVertex Γ) =
      (k+1)*cycleLength k N + Fintype.card (Link Γ)*(cycleLength k N - 3) := by
    simp [SourceVertex,DialVertex,ZMod.card]
  rw [hV]
  exact size_arith k _ _ (five_le_cycleLength k N) (hC ▸ hL)

end SourceWidth

/-! ## Main theorem -/

/-- Multicoloured Clique reduces to homomorphism into an odd cycle: decision
equivalence, source width at most `k+2`, target width at most two, and polynomial
size. The target `cyc n` is mathlib's `cycleGraph n` (`cyc_eq_cycleGraph`). -/
theorem reduction (Γ : SimpleGraph (Fin k × Fin N)) :
    (Nonempty (source Γ →g cyc (cycleLength k N)) ↔ MulticolouredClique Γ) ∧
    HasWidth (source Γ) (k+2) ∧ HasWidth (cyc (cycleLength k N)) 2 ∧
    Odd (cycleLength k N) ∧
    Fintype.card (SourceVertex Γ) ≤ (k+1)^2*(cycleLength k N)^2 :=
  ⟨source_hom_iff_clique Γ,source_width Γ,target_width _,cycleLength_odd k N,source_card_le Γ⟩

/-- The target of the reduction is mathlib's cycle graph of odd length. -/
theorem target_eq_cycleGraph (k N : ℕ) :
    cyc (cycleLength k N) = cycleGraph (cycleLength k N) :=
  cyc_eq_cycleGraph (2*halfLength k N)

/-- The same reduction stated with mathlib's cycle graph as the target. -/
theorem reduction_cycleGraph (Γ : SimpleGraph (Fin k × Fin N)) :
    (Nonempty (source Γ →g cycleGraph (cycleLength k N)) ↔ MulticolouredClique Γ) ∧
    HasWidth (source Γ) (k+2) ∧ HasWidth (cycleGraph (cycleLength k N)) 2 ∧
    Odd (cycleLength k N) ∧
    Fintype.card (SourceVertex Γ) ≤ (k+1)^2*(cycleLength k N)^2 := by
  have h1 := source_hom_iff_clique Γ
  have h2 := target_width (cycleLength k N)
  rw [target_eq_cycleGraph] at h1 h2
  exact ⟨h1,source_width Γ,h2,cycleLength_odd k N,source_card_le Γ⟩

end TreewidthHom.OddCycle
