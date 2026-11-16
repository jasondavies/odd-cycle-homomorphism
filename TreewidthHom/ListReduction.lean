module

public import TreewidthHom.ReferenceCycles
public import TreewidthHom.Links

@[expose] public section

/-!
# List Coloring reduces to homomorphism into an odd cycle

Every edge is replaced by an inequality link. A separate reference cycle for
each vertex/color pair, sharing the same ordered edge, enforces its list.
Copies for allowed colors are harmless and simplify the finite vertex type.
-/
namespace TreewidthHom.OddCycle.ListReduction
open SimpleGraph Reference

variable {m n : ℕ} [Fact (1 < n)]

abbrev Copies (m n : ℕ) := Fin m × ZMod n
abbrev Private (m n : ℕ) := Copies m n × Fin (n-2)
abbrev BaseVertex (m n : ℕ) := RefVertex (Copies m n) n ⊕ Fin m
abbrev Code (m n : ℕ) := Copies m n ⊕ (Fin m × Fin m)

def BaseRel : BaseVertex m n → BaseVertex m n → Prop
  | .inl u, .inl v =>
      (u = .inl 0 ∧ v = .inl 1) ∨ ∃ i d, u = ref i d ∧ v = ref i (d+1)
  | _, _ => False

def base (m n : ℕ) [Fact (1 < n)] : SimpleGraph (BaseVertex m n) :=
  .fromRel BaseRel

def Valid (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n)) : Code m n → Prop
  | .inl (v,d) => d ∉ L v
  | .inr (u,v) => u < v ∧ F.Adj u v

abbrev Link (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n)) :=
  {c : Code m n // Valid F L c}

def src : Code m n → BaseVertex m n
  | .inl (v,d) => .inl (ref (v,d) d)
  | .inr (u,_) => .inr u

def dst : Code m n → BaseVertex m n
  | .inl (v,_) => .inr v
  | .inr (_,v) => .inr v

abbrev SourceVertex (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n)) :=
  BaseVertex m n ⊕ (Link F L × Fin (n-3))

def source (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n)) :
    SimpleGraph (SourceVertex F L) :=
  linked (base m n) (fun l : Link F L => src l.val) (fun l => dst l.val) (n-3)

/-- A proper coloring whose values belong to the prescribed lists. -/
def Colorable (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n)) : Prop :=
  ∃ c : Fin m → ZMod n, (∀ v, c v ∈ L v) ∧ ∀ u v, F.Adj u v → c u ≠ c v

theorem base_anchor_adj : (base m n).Adj (.inl (.inl 0)) (.inl (.inl 1)) := by
  apply (fromRel_adj _ _ _).mpr
  exact ⟨by simp,Or.inl (Or.inl ⟨rfl,rfl⟩)⟩

theorem base_ref_adj (i : Copies m n) (d : ZMod n) :
    (base m n).Adj (.inl (ref i d)) (.inl (ref i (d+1))) := by
  refine (fromRel_adj _ _ _).mpr ⟨?_,Or.inl (Or.inr ⟨i,d,rfl,rfl⟩)⟩
  exact fun h => ref_ne i d (Sum.inl.inj h)

theorem private_step {i j : Copies m n} {a b : Fin (n-2)} {d : ZMod n}
    (ha : ref i d = .inr (i,a)) (hb : ref i (d+1) = .inr (j,b)) :
    i = j ∧ b.val = a.val+1 := by
  obtain ⟨_,hda⟩ := ref_private ha
  obtain ⟨hij,hdb⟩ := ref_private hb
  have hv : (d+1).val = (d.val+1)%n := by rw [ZMod.val_add,ZMod.val_one]
  have hd := ZMod.val_lt d
  refine ⟨hij.symm,?_⟩
  rcases Nat.lt_or_ge (d.val+1) n with hh | hh
  · rw [Nat.mod_eq_of_lt hh] at hv; omega
  · have : d.val+1=n := by omega
    rw [this,Nat.mod_self] at hv; omega

theorem private_adj {p r : Private m n}
    (h : (base m n).Adj (.inl (.inr p)) (.inl (.inr r))) :
    p.1 = r.1 ∧ (r.2.val = p.2.val+1 ∨ p.2.val = r.2.val+1) := by
  have step : ∀ p r : Private m n, BaseRel (.inl (.inr p)) (.inl (.inr r)) →
      p.1 = r.1 ∧ r.2.val = p.2.val+1 := by
    intro p r hh
    rcases hh with ⟨h,_⟩ | ⟨i,d,hp,hr⟩
    · cases h
    · have hi := (ref_private hp.symm).1
      have hp' : ref p.1 d = .inr (p.1,p.2) := by simpa [← hi] using hp.symm
      have hr' : ref p.1 (d+1) = .inr (r.1,r.2) := by simpa [← hi] using hr.symm
      exact private_step hp' hr'
  obtain ⟨_,h | h⟩ := (fromRel_adj _ _ _).mp h
  · obtain ⟨he,hh⟩ := step p r h; exact ⟨he,Or.inl hh⟩
  · obtain ⟨he,hh⟩ := step r p h; exact ⟨he.symm,Or.inr hh⟩

theorem source_hom_iff (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    (hodd : Odd n) (hn : 5 ≤ n) :
    Nonempty (source F L →g cyc n) ↔
      ∃ φ : base m n →g cyc n, ∀ l : Link F L, φ (src l.val) ≠ φ (dst l.val) := by
  have hq : n-3+1 = n-2 := by omega
  unfold source
  rw [linked_hom_iff _ _ _ _ (by omega)]
  constructor
  · rintro ⟨φ,h⟩
    refine ⟨φ,fun l => ?_⟩
    obtain ⟨w,h0,h1,hs⟩ := h l
    rw [hq] at h1
    exact (walk_iff_ne hodd (by omega) _ _).mp
      ⟨w,h0,h1,fun t ht => (cyc_adj _ _).mp (hs t (by omega))⟩
  · rintro ⟨φ,h⟩
    refine ⟨φ,fun l => ?_⟩
    obtain ⟨w,h0,h1,hs⟩ := (walk_iff_ne hodd (by omega) _ _).mpr (h l)
    exact ⟨w,h0,by simpa [hq] using h1,fun i hi => (cyc_adj _ _).mpr (hs i (by omega))⟩

theorem hom_of_coloring (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    (hodd : Odd n) (hn : 5 ≤ n) (h : Colorable F L) :
    Nonempty (source F L →g cyc n) := by
  obtain ⟨c,hL,hc⟩ := h
  rw [source_hom_iff F L hodd hn]
  let f : BaseVertex m n → ZMod n := Sum.elim coord c
  have hf : ∀ x y, BaseRel x y → Near (f x) (f y) := by
    rintro (x | x) (y | y) h <;> try exact h.elim
    rcases h with ⟨rfl,rfl⟩ | ⟨i,d,rfl,rfl⟩
    · exact Or.inl (by simp [f,coord])
    · change Near (coord (ref i d)) (coord (ref i (d+1)))
      rw [coord_ref,coord_ref]
      exact Or.inl rfl
  refine ⟨⟨f,?_⟩,?_⟩
  · intro x y hxy
    obtain ⟨_,h | h⟩ := (fromRel_adj _ _ _).mp hxy
    · exact (cyc_adj _ _).mpr (hf x y h)
    · exact (cyc_adj _ _).mpr (hf y x h).symm
  · rintro ⟨(⟨v,d⟩ | ⟨u,v⟩),h⟩
    · change coord (ref (v,d) d) ≠ c v
      rw [coord_ref]
      exact fun he => h (he ▸ hL v)
    · exact hc u v h.2

theorem coloring_of_hom (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    (hodd : Odd n) (hn : 5 ≤ n) (h : Nonempty (source F L →g cyc n)) :
    Colorable F L := by
  classical
  obtain ⟨φ,hlink⟩ := (source_hom_iff F L hodd hn).mp h
  let r := φ (.inl (.inl 0))
  let ε := φ (.inl (.inl 1)) - r
  have hε : ε = 1 ∨ ε = -1 := by
    rcases (cyc_adj _ _).mp (φ.map_rel base_anchor_adj) with h | h
    · left; dsimp [ε,r]; rw [h]; ring
    · right; dsimp [ε,r]; rw [h]; ring
  have hsq : ε*ε = 1 := by rcases hε with h | h <;> rw [h] <;> ring
  have href : ∀ i : Copies m n, ∀ d, φ (.inl (ref i d)) = r+ε*d := by
    intro i
    obtain ⟨r',ε',_,hf⟩ := rotation_or_reflection hodd (fun d => φ (.inl (ref i d)))
      (fun d => (cyc_adj _ _).mp (φ.map_rel (base_ref_adj i d)))
    have h0 : r' = r := by simpa [r] using (hf 0).symm
    have h1 : ε' = ε := by
      have h := hf 1
      simp only [ref_one,mul_one,h0] at h
      dsimp [ε]
      rw [h]; ring
    simpa [h0,h1] using hf
  let c : Fin m → ZMod n := fun v => ε*(φ (.inr v)-r)
  have hc : ∀ v, φ (.inr v) = r+ε*c v := by
    intro v
    dsimp [c]
    linear_combination -(φ (.inr v)-r)*hsq
  refine ⟨c,?_,?_⟩
  · intro v
    by_contra hnot
    have h := hlink ⟨.inl (v,c v),hnot⟩
    apply h
    change φ (.inl (ref (v,c v) (c v))) = φ (.inr v)
    rw [href,hc]
  · intro u v huv he
    have distinct : φ (.inr u) ≠ φ (.inr v) := by
      rcases lt_or_gt_of_ne (F.ne_of_adj huv) with hlt | hlt
      · exact hlink ⟨.inr (u,v),hlt,huv⟩
      · exact (hlink ⟨.inr (v,u),hlt,huv.symm⟩).symm
    exact distinct (by rw [hc,hc,he])

/-- Decision equivalence, for arbitrary lists over the target cycle. -/
theorem source_hom_iff_colorable (F : SimpleGraph (Fin m))
    (L : Fin m → Finset (ZMod n)) (hodd : Odd n) (hn : 5 ≤ n) :
    Nonempty (source F L →g cyc n) ↔ Colorable F L :=
  ⟨coloring_of_hom F L hodd hn,hom_of_coloring F L hodd hn⟩

end TreewidthHom.OddCycle.ListReduction
