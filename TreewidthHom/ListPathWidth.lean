module

public import TreewidthHom.ListWidth
public import TreewidthHom.PathIntervals

@[expose] public section

namespace TreewidthHom.OddCycle.ListReduction
open SimpleGraph Reference
variable {m n : ℕ} [Fact (1 < n)]

def privateRank (p : Private m n) : ℕ :=
  (p.1.1.val*n+p.1.2.val)*(n-2)+p.2.val

theorem privateRank_lt (p : Private m n) : privateRank p < m*n*(n-2) := by
  have h1 := p.1.1.isLt
  have h2 := ZMod.val_lt p.1.2
  have h3 := p.2.isLt
  have h4 : (p.1.1.val+1)*n ≤ m*n := Nat.mul_le_mul_right n h1
  have h5 : p.1.1.val*n+p.1.2.val < m*n := by
    have : (p.1.1.val+1)*n = p.1.1.val*n+n := by ring
    omega
  have h6 : (p.1.1.val*n+p.1.2.val+1)*(n-2) ≤ m*n*(n-2) := Nat.mul_le_mul_right (n-2) h5
  have : (p.1.1.val*n+p.1.2.val+1)*(n-2) =
      (p.1.1.val*n+p.1.2.val)*(n-2)+(n-2) := by ring
  dsimp [privateRank]; omega

theorem privateRank_injective : Function.Injective (privateRank (m := m) (n := n)) := by
  intro p r h
  have hp := p.2.isLt
  have hr := r.2.isLt
  have he : p.1.1.val*n+p.1.2.val = r.1.1.val*n+r.1.2.val := by
    have he := congrArg (fun a => a/(n-2)) h
    simpa only [privateRank,mul_add_div_of_lt hp,mul_add_div_of_lt hr] using he
  have hpn := ZMod.val_lt p.1.2
  have hrn := ZMod.val_lt r.1.2
  have he1 : p.1.1.val = r.1.1.val := by
    have hh := congrArg (fun a => a/n) he
    simpa only [mul_add_div_of_lt hpn,mul_add_div_of_lt hrn] using hh
  have he2 : p.1.2.val = r.1.2.val := by rw [he1] at he; omega
  have he3 : p.2.val=r.2.val := by dsimp [privateRank] at h; rw [he1,he2] at h; omega
  exact Prod.ext (Prod.ext (Fin.ext he1) (ZMod.val_injective _ he2)) (Fin.ext he3)

theorem aug_pathWidth (F : SimpleGraph (Fin m)) {w : ℕ} (hw : HasPathWidth F w) :
    HasPathWidth (aug (n := n) F) (w+4) := by
  classical
  obtain ⟨d,R,D,hw⟩ := hw
  obtain ⟨lo,hi,hlohi,hhi,hmem⟩ := D.path_intervals
  let C := m*n*(n-2)
  let S := 2*(C+2)
  let P := (R+1)*S-1
  have hS : 0 < S := by dsimp [S]; omega
  let time : Private m n → ℕ := fun p => lo p.1.1*S+2*privateRank p+2
  have bounds : ∀ p, lo p.1.1*S+1 ≤ time p ∧ time p+1 < (lo p.1.1+1)*S := by
    intro p
    have hh := privateRank_lt p
    change privateRank p < C at hh
    have he : (lo p.1.1+1)*S = lo p.1.1*S+S := by ring
    dsimp [time,S] at *; omega
  have divtime : ∀ p, time p/S = lo p.1.1 := by
    intro p; apply Nat.div_eq_of_lt_le <;> have := bounds p <;> omega
  have time_inj : Function.Injective time := by
    intro p r h
    have he : lo p.1.1=lo r.1.1 := by rw [← divtime p,← divtime r,h]
    apply privateRank_injective
    dsimp [time] at h; rw [he] at h; omega
  let low : BaseVertex m n → ℕ
    | .inl (.inl _) => 0
    | .inl (.inr p) => time p-1
    | .inr v => lo v*S
  let high : BaseVertex m n → ℕ
    | .inl (.inl _) => P
    | .inl (.inr p) => time p+1
    | .inr v => (hi v+1)*S-1
  have hlast : ∀ v, (hi v+1)*S ≤ (R+1)*S := fun v => Nat.mul_le_mul_right S (by have := hhi v; omega)
  have hgap : ∀ v, lo v*S < (hi v+1)*S := fun v =>
    Nat.mul_lt_mul_of_pos_right (by have := hlohi v; omega) hS
  have lowhigh : ∀ x, low x ≤ high x := by
    rintro ((a | p) | v)
    · exact Nat.zero_le _
    · change time p-1 ≤ time p+1; omega
    · have := hgap v; change lo v*S ≤ (hi v+1)*S-1; omega
  have highP : ∀ x, high x ≤ P := by
    rintro ((a | p) | v)
    · exact le_rfl
    · have hh := bounds p
      have h1 := Nat.mul_le_mul_right S (hlohi p.1.1)
      have h2 := hlast p.1.1
      have he : (lo p.1.1+1)*S=lo p.1.1*S+S := by ring
      have he' : (hi p.1.1+1)*S=hi p.1.1*S+S := by ring
      change time p+1 ≤ (R+1)*S-1; omega
    · exact Nat.sub_le_sub_right (hlast v) 1
  have hub_time : ∀ p, low (.inr p.1.1) ≤ time p ∧ time p ≤ high (.inr p.1.1) := by
    intro p
    have hh := bounds p
    have h1 := Nat.mul_le_mul_right S (Nat.add_le_add_right (hlohi p.1.1) 1)
    change lo p.1.1*S ≤ time p ∧ time p ≤ (hi p.1.1+1)*S-1
    omega
  have hub_at : ∀ v b, lo v ≤ b → b ≤ hi v →
      low (.inr v) ≤ b*S ∧ b*S ≤ high (.inr v) := by
    intro v b h1 h2
    have h3 := Nat.mul_le_mul_right S h1
    have h4 := Nat.mul_lt_mul_of_pos_right (by omega : b < hi v+1) hS
    change lo v*S ≤ b*S ∧ b*S ≤ (hi v+1)*S-1
    omega
  have mixed : ∀ x v, (∃ d, x=ref (v,d) d) →
      low (.inl x) ≤ high (.inr v) ∧ low (.inr v) ≤ high (.inl x) := by
    intro x v h
    obtain ⟨d,rfl⟩ := h
    rcases he : ref (v,d) d with a | p
    · exact ⟨Nat.zero_le _,(lowhigh (.inr v)).trans (highP (.inr v))⟩
    · have hv : p.1.1=v := congrArg Prod.fst (ref_private he).1
      have hh := hub_time p
      rw [hv] at hh
      change time p-1 ≤ high (.inr v) ∧ low (.inr v) ≤ time p+1
      omega
  have edges : ∀ x y, (aug F).Adj x y → low x ≤ high y ∧ low y ≤ high x := by
    rintro (x | u) (y | v) h
    · rcases x with a | p <;> rcases y with b | r
      · exact ⟨Nat.zero_le _,Nat.zero_le _⟩
      · change 0 ≤ time r+1 ∧ time r-1 ≤ P
        have hh := highP (.inl (.inr r))
        change time r+1 ≤ P at hh
        omega
      · change time p-1 ≤ P ∧ 0 ≤ time p+1
        have hh := highP (.inl (.inr p))
        change time p+1 ≤ P at hh
        omega
      · obtain ⟨he,hh⟩ := private_adj h
        have close : ∀ p r : Private m n, p.1=r.1 → r.2.val=p.2.val+1 → time r=time p+2 := by
          intro p r he hh
          dsimp [time,privateRank]
          rw [← he,hh]; ring
        rcases hh with hh | hh
        · have := close p r he hh
          change time p-1 ≤ time r+1 ∧ time r-1 ≤ time p+1; omega
        · have := close r p he.symm hh
          change time p-1 ≤ time r+1 ∧ time r-1 ≤ time p+1; omega
    · exact mixed x v h
    · exact (mixed y u h).symm
    · obtain ⟨b,hu,hv⟩ := D.edge_cover h
      have hu' := (hmem _ _).mp hu
      have hv' := (hmem _ _).mp hv
      have h1 := hub_at u b.val hu'.1 hu'.2
      have h2 := hub_at v b.val hv'.1 hv'.2
      omega
  apply hasPathWidth_of_intervals (aug F) P (w+4) low high lowhigh highP edges
  intro t
  let hubs := Finset.univ.filter (fun v : Fin m => low (.inr v) ≤ t ∧ t ≤ high (.inr v))
  let inner := Finset.univ.filter (fun p : Private m n => time p-1 ≤ t ∧ t ≤ time p+1)
  have hinner : inner.card ≤ 2 := by
    have hsub : ∀ p ∈ inner, time p ∈ ({2*(t/2),2*(t/2+1)} : Finset ℕ) := by
      intro p hp
      have hh : time p-1 ≤ t ∧ t ≤ time p+1 := (Finset.mem_filter.mp hp).2
      have hp0 := (bounds p).1
      have heven : time p % 2 = 0 := by simp [time,S,Nat.add_mod,Nat.mul_mod]
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
    exact (Finset.card_le_card_of_injOn time hsub time_inj.injOn).trans Finset.card_le_two
  have hhubs : hubs.card ≤ w+1 := by
    by_cases ht : t ≤ P
    · have hdiv : t/S ≤ R := by
        have hmul : t < (R+1)*S := by dsimp [P] at ht; have := Nat.mul_pos (by omega : 0<R+1) hS; omega
        have := (Nat.div_lt_iff_lt_mul hS).mpr hmul; omega
      apply (Finset.card_le_card (t := D.bag ⟨t/S,by omega⟩) ?_).trans (hw _)
      intro v hv
      have hh : lo v*S ≤ t ∧ t ≤ (hi v+1)*S-1 := (Finset.mem_filter.mp hv).2
      apply (hmem _ _).mpr
      have h1 := (Nat.le_div_iff_mul_le hS).mpr hh.1
      have hpos : 0 < (hi v+1)*S := Nat.mul_pos (by omega) hS
      have h2 := (Nat.div_lt_iff_lt_mul hS).mpr (show t < (hi v+1)*S by omega)
      change lo v ≤ t/S ∧ t/S ≤ hi v
      exact ⟨h1,by omega⟩
    · have he : hubs=∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro v hv
        have hh := (Finset.mem_filter.mp hv).2.2
        have := highP (.inr v); omega
      simp [he]
  let eH : Fin m ↪ BaseVertex m n := ⟨Sum.inr,Sum.inr_injective⟩
  let eA : Fin 2 ↪ BaseVertex m n := ⟨fun a => .inl (.inl a),fun _ _ h => Sum.inl.inj (Sum.inl.inj h)⟩
  let eP : Private m n ↪ BaseVertex m n := ⟨fun p => .inl (.inr p),fun _ _ h => Sum.inr.inj (Sum.inl.inj h)⟩
  have hsub : Finset.univ.filter (fun x => low x ≤ t ∧ t ≤ high x) ⊆
      hubs.map eH ∪ (Finset.univ.map eA ∪ inner.map eP) := by
    rintro ((a | p) | v) hx
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_map.mpr ⟨a,Finset.mem_univ _,rfl⟩))
    · have hp : p ∈ inner := by simpa [low,high,inner] using hx
      exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨p,hp,rfl⟩))
    · have hv : v ∈ hubs := by simpa [hubs] using hx
      exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨v,hv,rfl⟩)
  have hc := Finset.card_le_card hsub
  have hc1 := Finset.card_union_le (hubs.map eH) (Finset.univ.map eA ∪ inner.map eP)
  have hc2 := Finset.card_union_le (Finset.univ.map eA) (inner.map eP)
  simp only [Finset.card_map,Finset.card_univ,Fintype.card_fin] at hc1 hc2
  omega

/-- A conservative additive bound, factoring through the auxiliary graph. -/
theorem source_pathWidth (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    (hn : 5 ≤ n) {w : ℕ} (hw : HasPathWidth F w) : HasPathWidth (source F L) (w+6) := by
  classical
  exact pathWidth_linked_of_bags (base m n) (base_le_aug F)
    (fun l : Link F L => src l.val) (fun l => dst l.val) (n-3) (by omega)
    (aug_pathWidth F hw) (link_adj_aug F L)

end TreewidthHom.OddCycle.ListReduction
