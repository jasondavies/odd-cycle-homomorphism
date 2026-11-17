module

public import TreewidthHom.Width
public import TreewidthHom.IntervalDecomposition
public import TreewidthHom.Links

@[expose] public section

/-!
# Path decompositions

`HasPathWidth G w` is a decomposition certificate whose bags are arranged along a
path. The main lemma builds one for a graph with attached paths (`linked`): the
base vertices occupy intervals of positions, and every attached path is swept at
one position at which both of its ends are present.
-/
namespace TreewidthHom
open SimpleGraph

/-- A supplied path-decomposition certificate of width at most w. -/
def HasPathWidth {V : Type} (G : SimpleGraph V) (w : ℕ) : Prop := by
  exact ∃ d : DecidableEq V, ∃ n : ℕ,
    ∃ D : @Decomposition V (Fin (n+1)) d G (pathGraph (n+1)), ∀ b, (D.bag b).card ≤ w+1

/-- A path certificate with an explicit upper bound on its number of bags. -/
def HasPathWidthWithBags {V : Type} (G : SimpleGraph V) (w N : ℕ) : Prop :=
  ∃ d : DecidableEq V, ∃ r : ℕ,
    ∃ D : @Decomposition V (Fin (r+1)) d G (pathGraph (r+1)),
      (∀ b, (D.bag b).card ≤ w+1) ∧ r+1 ≤ N

theorem HasPathWidthWithBags.hasPathWidth {V : Type} {G : SimpleGraph V} {w N : ℕ}
    (h : HasPathWidthWithBags G w N) : HasPathWidth G w := by
  obtain ⟨d, r, D, hD, _⟩ := h
  exact ⟨d, r, D, hD⟩

theorem HasPathWidth.hasWidth {V : Type} {G : SimpleGraph V} {w : ℕ}
    (h : HasPathWidth G w) : HasWidth G w := by
  obtain ⟨d,n,D,hw⟩ := h
  exact ⟨d,_,_,D,hw⟩

theorem HasPathWidth.mono {V : Type} {G : SimpleGraph V} {a b : ℕ}
    (h : HasPathWidth G a) (hab : a ≤ b) : HasPathWidth G b := by
  obtain ⟨d,n,D,hw⟩ := h
  exact ⟨d,n,D,fun c => (hw c).trans (Nat.add_le_add_right hab 1)⟩

/-- Recover the leading index when the final offset is smaller than the block. -/
theorem mul_add_div_of_lt {a b c : ℕ} (hc : c < b) : (a*b+c)/b=a := by
  simpa [Nat.add_comm, Nat.div_eq_of_lt hc] using
    Nat.add_mul_div_right c a (Nat.zero_lt_of_lt hc)

/-- Position of a time, when every position lasts `J*a` time units. -/
theorem time_div {J a p s c : ℕ} (hs : s < J) (hc : c < a) :
    ((p*J+s)*a+c) / (J*a) = p := by
  rw [Nat.mul_comm J a, ← Nat.div_div_eq_div_mul]
  rw [mul_add_div_of_lt hc, mul_add_div_of_lt hs]

/-- The sweep of a link determines the link. -/
theorem time_slot {J a p s c p' s' c' : ℕ} (hs : s < J) (hs' : s' < J) (hc : c < a) (hc' : c' < a)
    (h : (p*J+s)*a+c = (p'*J+s')*a+c') : p = p' ∧ s = s' := by
  have hslot := congrArg (fun x => x/a) h
  simp only [mul_add_div_of_lt hc, mul_add_div_of_lt hc'] at hslot
  have hp := congrArg (fun x => x/J) hslot
  simp only [mul_add_div_of_lt hs, mul_add_div_of_lt hs'] at hp
  exact ⟨hp, by rw [hp] at hslot; omega⟩

/-- A path decomposition of a graph with attached paths. Base vertex `x` occupies
the positions `lo x,...,hi x`. Link `l` is swept at position `pos l`, in slot
`slot l`, while both of its ends are present. If at most `w+1` base vertices are
present at any position, and at most `w-1` at the position of any link, the
width is at most `w`. -/
theorem pathWidth_linked_bag_bound {V₀ L : Type} [Fintype V₀] [Fintype L]
    (B : SimpleGraph V₀) (s t : L → V₀) (q : ℕ) (hq : 0 < q) (P J w : ℕ)
    (lo hi : V₀ → ℕ) (hlohi : ∀ x, lo x ≤ hi x) (hhi : ∀ x, hi x ≤ P)
    (hB : ∀ x y, B.Adj x y → lo x ≤ hi y ∧ lo y ≤ hi x)
    (pos slot : L → ℕ) (hslot : ∀ l, slot l < J)
    (hinj : ∀ l l', pos l = pos l' → slot l = slot l' → l = l')
    (hs : ∀ l, lo (s l) ≤ pos l ∧ pos l ≤ hi (s l))
    (ht : ∀ l, lo (t l) ≤ pos l ∧ pos l ≤ hi (t l))
    (hbase : ∀ p, (Finset.univ.filter (fun x => lo x ≤ p ∧ p ≤ hi x)).card ≤ w+1)
    (hlink : ∀ l, (Finset.univ.filter (fun x => lo x ≤ pos l ∧ pos l ≤ hi x)).card + 2 ≤ w+1) :
    HasPathWidthWithBags (linked B s t q) w ((P+1)*((J+1)*(q+1))) := by
  classical
  -- one extra slot keeps the time unit positive even without links
  let J' := J+1
  let a := q+1
  let U := J'*a
  have hU : 0 < U := Nat.mul_pos (by omega) (by omega)
  let start : L → ℕ := fun l => (pos l*J'+slot l)*a
  have hslot' : ∀ l, slot l < J' := fun l => by have := hslot l; omega
  have hdiv : ∀ l c, c < a → (start l + c)/U = pos l := fun l c hc => time_div (hslot' l) hc
  let act : V₀ ⊕ (L × Fin q) → ℕ → Prop := fun v τ => match v with
    | .inl x => lo x ≤ τ/U ∧ τ/U ≤ hi x
    | .inr (l,c) => τ = start l + c.val ∨ τ = start l + c.val + 1
  let n := (P+1)*U
  have hn : 0 < n := Nat.mul_pos (by omega) hU
  have hrange : ∀ l c, c < a → start l + c < n := by
    intro l c hc
    have h1 := hdiv l c hc
    have h2 : pos l ≤ P := (hs l).2.trans (hhi _)
    have h3 : (start l + c)/U < P+1 := by omega
    exact (Nat.div_lt_iff_lt_mul hU).mp h3
  let bag : Fin (n-1+1) → Finset (V₀ ⊕ (L × Fin q)) := fun τ =>
    Finset.univ.filter (fun v => act v τ.val)
  have hmem : ∀ v τ, v ∈ bag τ ↔ act v τ.val := by
    intro v τ
    simp [bag]
  have hfin : ∀ τ : ℕ, τ < n → τ < n-1+1 := by intro τ h; omega
  let D : Decomposition (linked B s t q) (pathGraph (n-1+1)) :=
    intervalDecomposition (linked B s t q) (n-1) bag
      (by
        rintro (x | ⟨l,c⟩)
        · have h1 : lo x*U < n := by
            have : lo x ≤ P := (hlohi x).trans (hhi x)
            exact Nat.mul_lt_mul_of_pos_right (by omega) hU
          refine ⟨⟨lo x*U,hfin _ h1⟩,(hmem _ _).mpr ?_⟩
          change lo x ≤ lo x*U/U ∧ lo x*U/U ≤ hi x
          rw [Nat.mul_div_cancel _ hU]
          exact ⟨le_rfl,hlohi x⟩
        · have h1 := hrange l c.val (by have := c.isLt; omega)
          exact ⟨⟨start l + c.val,hfin _ h1⟩,(hmem _ _).mpr (Or.inl rfl)⟩)
      (by
        rintro (x | ⟨l,c⟩) (y | ⟨l',c'⟩) h
        · have hxy := hB x y h
          let p := max (lo x) (lo y)
          have hp1 : p ≤ hi x := max_le (hlohi x) hxy.2
          have hp2 : p ≤ hi y := max_le hxy.1 (hlohi y)
          have h1 : p*U < n := by
            have : p ≤ P := hp1.trans (hhi x)
            exact Nat.mul_lt_mul_of_pos_right (by omega) hU
          refine ⟨⟨p*U,hfin _ h1⟩,(hmem _ _).mpr ?_,(hmem _ _).mpr ?_⟩
          · change lo x ≤ p*U/U ∧ p*U/U ≤ hi x
            rw [Nat.mul_div_cancel _ hU]
            exact ⟨le_max_left _ _,hp1⟩
          · change lo y ≤ p*U/U ∧ p*U/U ≤ hi y
            rw [Nat.mul_div_cancel _ hU]
            exact ⟨le_max_right _ _,hp2⟩
        · have h' : (c'.val = 0 ∧ x = s l') ∨ (c'.val+1 = q ∧ x = t l') := h
          rcases h' with ⟨hc,rfl⟩ | ⟨hc,rfl⟩
          · have h1 := hrange l' 0 (by omega)
            refine ⟨⟨start l' + 0,hfin _ h1⟩,(hmem _ _).mpr ?_,(hmem _ _).mpr (Or.inl (by simp [hc]))⟩
            change lo (s l') ≤ (start l' + 0)/U ∧ (start l' + 0)/U ≤ hi (s l')
            rw [hdiv l' 0 (by omega)]
            exact hs l'
          · have h1 := hrange l' q (by omega)
            refine ⟨⟨start l' + q,hfin _ h1⟩,(hmem _ _).mpr ?_,(hmem _ _).mpr (Or.inr (by simp; omega))⟩
            change lo (t l') ≤ (start l' + q)/U ∧ (start l' + q)/U ≤ hi (t l')
            rw [hdiv l' q (by omega)]
            exact ht l'
        · have h' : (c.val = 0 ∧ y = s l) ∨ (c.val+1 = q ∧ y = t l) := h
          rcases h' with ⟨hc,rfl⟩ | ⟨hc,rfl⟩
          · have h1 := hrange l 0 (by omega)
            refine ⟨⟨start l + 0,hfin _ h1⟩,(hmem _ _).mpr (Or.inl (by simp [hc])),(hmem _ _).mpr ?_⟩
            change lo (s l) ≤ (start l + 0)/U ∧ (start l + 0)/U ≤ hi (s l)
            rw [hdiv l 0 (by omega)]
            exact hs l
          · have h1 := hrange l q (by omega)
            refine ⟨⟨start l + q,hfin _ h1⟩,(hmem _ _).mpr (Or.inr (by simp; omega)),(hmem _ _).mpr ?_⟩
            change lo (t l) ≤ (start l + q)/U ∧ (start l + q)/U ≤ hi (t l)
            rw [hdiv l q (by omega)]
            exact ht l
        · obtain ⟨hl,hcc⟩ : l = l' ∧ (c'.val = c.val+1 ∨ c.val = c'.val+1) := h
          subst hl
          rcases hcc with h1 | h1
          · have h2 := hrange l c'.val (by have := c'.isLt; omega)
            exact ⟨⟨start l + c'.val,hfin _ h2⟩,(hmem _ _).mpr (Or.inr (by simp; omega)),
              (hmem _ _).mpr (Or.inl rfl)⟩
          · have h2 := hrange l c.val (by have := c.isLt; omega)
            exact ⟨⟨start l + c.val,hfin _ h2⟩,(hmem _ _).mpr (Or.inl rfl),
              (hmem _ _).mpr (Or.inr (by simp; omega))⟩)
      (by
        rintro (x | ⟨l,c⟩) τ1 τ2 τ3 h13 h32 h1 h2
        · have a1 : lo x ≤ τ1.val/U ∧ τ1.val/U ≤ hi x := (hmem _ _).mp h1
          have a2 : lo x ≤ τ2.val/U ∧ τ2.val/U ≤ hi x := (hmem _ _).mp h2
          have d1 : τ1.val/U ≤ τ3.val/U := Nat.div_le_div_right h13
          have d2 : τ3.val/U ≤ τ2.val/U := Nat.div_le_div_right h32
          exact (hmem _ _).mpr ⟨by omega,by omega⟩
        · have a1 : τ1.val = start l + c.val ∨ τ1.val = start l + c.val + 1 := (hmem _ _).mp h1
          have a2 : τ2.val = start l + c.val ∨ τ2.val = start l + c.val + 1 := (hmem _ _).mp h2
          have b1 : τ1.val ≤ τ3.val := h13
          have b2 : τ3.val ≤ τ2.val := h32
          refine (hmem _ _).mpr ?_
          change τ3.val = start l + c.val ∨ τ3.val = start l + c.val + 1
          omega)
  refine ⟨inferInstance,n-1,D,?_,by dsimp [n, U, J', a] at *; omega⟩
  intro τ
  change (bag τ).card ≤ w+1
  let p := τ.val/U
  let baseSet : Finset V₀ := Finset.univ.filter (fun x => lo x ≤ p ∧ p ≤ hi x)
  let inner : Finset (L × Fin q) := Finset.univ.filter
    (fun lc => τ.val = start lc.1 + lc.2.val ∨ τ.val = start lc.1 + lc.2.val + 1)
  have hsub : bag τ ⊆ baseSet.map ⟨Sum.inl,Sum.inl_injective⟩ ∪ inner.map ⟨Sum.inr,Sum.inr_injective⟩ := by
    rintro (x | ⟨l,c⟩) hv
    · have hx : lo x ≤ p ∧ p ≤ hi x := (hmem _ _).mp hv
      simp [baseSet,hx]
    · have hx : τ.val = start l + c.val ∨ τ.val = start l + c.val + 1 := (hmem _ _).mp hv
      simp [inner,hx]
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simp only [Finset.card_map] at hcard
  have hsame : ∀ lc ∈ inner, ∀ lc' ∈ inner, lc.1 = lc'.1 := by
    intro lc hlc lc' hlc'
    have h1 : τ.val = start lc.1 + lc.2.val ∨ τ.val = start lc.1 + lc.2.val + 1 := by
      simpa [inner] using hlc
    have h2 : τ.val = start lc'.1 + lc'.2.val ∨ τ.val = start lc'.1 + lc'.2.val + 1 := by
      simpa [inner] using hlc'
    have c1 := lc.2.isLt
    have c2 := lc'.2.isLt
    obtain ⟨e1,he1,hτ1⟩ : ∃ e, e < a ∧ τ.val = start lc.1 + e := by
      rcases h1 with h | h
      · exact ⟨lc.2.val,by omega,h⟩
      · exact ⟨lc.2.val+1,by omega,h⟩
    obtain ⟨e2,he2,hτ2⟩ : ∃ e, e < a ∧ τ.val = start lc'.1 + e := by
      rcases h2 with h | h
      · exact ⟨lc'.2.val,by omega,h⟩
      · exact ⟨lc'.2.val+1,by omega,h⟩
    obtain ⟨hp,hsl⟩ := time_slot (hslot' lc.1) (hslot' lc'.1) he1 he2 (hτ1.symm.trans hτ2)
    exact hinj _ _ hp hsl
  have hinner : inner.card ≤ 2 := by
    have h := Finset.card_le_card_of_injOn (s := inner) (t := Finset.range 2)
      (fun lc => τ.val - start lc.1 - lc.2.val)
      (by
        intro lc hlc
        have h1 : τ.val = start lc.1 + lc.2.val ∨ τ.val = start lc.1 + lc.2.val + 1 := by
          simpa [inner] using hlc
        simp only [Finset.coe_range,Set.mem_Iio]
        omega)
      (by
        intro lc hlc lc' hlc' heq
        have hl := hsame lc hlc lc' hlc'
        have h1 : τ.val = start lc.1 + lc.2.val ∨ τ.val = start lc.1 + lc.2.val + 1 := by
          simpa [inner] using hlc
        have h2 : τ.val = start lc'.1 + lc'.2.val ∨ τ.val = start lc'.1 + lc'.2.val + 1 := by
          simpa [inner] using hlc'
        dsimp only at heq
        rw [← hl] at h2 heq
        exact Prod.ext hl (Fin.ext (by omega)))
    simpa using h
  by_cases hempty : inner = ∅
  · have h0 : inner.card = 0 := by rw [hempty]; rfl
    have hb := hbase p
    change baseSet.card ≤ w+1 at hb
    omega
  · obtain ⟨lc,hlc⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have h1 : τ.val = start lc.1 + lc.2.val ∨ τ.val = start lc.1 + lc.2.val + 1 := by
      simpa [inner] using hlc
    have c1 := lc.2.isLt
    have hp : p = pos lc.1 := by
      rcases h1 with h | h
      · change τ.val/U = _
        rw [h]
        exact hdiv lc.1 _ (by omega)
      · change τ.val/U = _
        rw [h,Nat.add_assoc]
        exact hdiv lc.1 _ (by omega)
    have hb := hlink lc.1
    rw [← hp] at hb
    change baseSet.card + 2 ≤ w+1 at hb
    omega

theorem hasPathWidth_linked {V₀ L : Type} [Fintype V₀] [Fintype L]
    (B : SimpleGraph V₀) (s t : L → V₀) (q : ℕ) (hq : 0 < q) (P J w : ℕ)
    (lo hi : V₀ → ℕ) (hlohi : ∀ x, lo x ≤ hi x) (hhi : ∀ x, hi x ≤ P)
    (hB : ∀ x y, B.Adj x y → lo x ≤ hi y ∧ lo y ≤ hi x)
    (pos slot : L → ℕ) (hslot : ∀ l, slot l < J)
    (hinj : ∀ l l', pos l = pos l' → slot l = slot l' → l = l')
    (hs : ∀ l, lo (s l) ≤ pos l ∧ pos l ≤ hi (s l))
    (ht : ∀ l, lo (t l) ≤ pos l ∧ pos l ≤ hi (t l))
    (hbase : ∀ p, (Finset.univ.filter (fun x => lo x ≤ p ∧ p ≤ hi x)).card ≤ w+1)
    (hlink : ∀ l, (Finset.univ.filter (fun x => lo x ≤ pos l ∧ pos l ≤ hi x)).card + 2 ≤ w+1) :
    HasPathWidth (linked B s t q) w := by
  exact (pathWidth_linked_bag_bound B s t q hq P J w lo hi hlohi hhi hB
    pos slot hslot hinj hs ht hbase hlink).hasPathWidth

end TreewidthHom
