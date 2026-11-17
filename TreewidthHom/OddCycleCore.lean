module

public import TreewidthHom.BinaryTarget
public import TreewidthHom.OddGirth
public import TreewidthHom.ListSparse

@[expose] public section

/-!
# Homomorphic equivalence to an odd cycle

The recognition problem is expressed by homomorphisms in both directions.
Odd cycles are cores: their endomorphisms are injective. The reduction can
discard the target because its length is forced by the source girth.
-/

namespace TreewidthHom.OddCycle
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

/-- The usual endomorphism characterisation of a finite core. -/
def IsCore {W : Type*} (H : SimpleGraph W) : Prop :=
  ∀ f : H →g H, Function.Injective f

theorem cycle_isCore [Fact (1 < n)] (hn : Odd n) : IsCore (cyc n) := by
  intro f
  obtain ⟨r, ε, hε, hf⟩ := rotation_or_reflection hn f (fun x =>
    (cyc_adj _ _).mp (f.map_adj ((cyc_adj _ _).mpr (Or.inl rfl))))
  intro x y hxy
  rw [hf, hf] at hxy
  rcases hε with hε | hε <;> simp_all

/-- The input is homomorphically equivalent to an odd cycle. Since odd cycles
are cores, this is the target-free recognition problem from the manuscript. -/
def HasOddCycleCore (G : SimpleGraph V) : Prop :=
  ∃ k : ℕ, 3 ≤ k ∧ Odd k ∧ Nonempty (G →g cyc k) ∧ Nonempty (cyc k →g G)

theorem cycle_not_bipartite [Fact (1 < n)] (hn : Odd n) : ¬ (cyc n).IsBipartite := by
  intro hb
  let : Fact (1 < n + 2) := ⟨by have := Fact.out (p := 1 < n); omega⟩
  obtain ⟨f⟩ := hom_of_bipartite (n := n + 2) hb
  have := length_le_of_hom hn f
  omega

private theorem cycle_length_le_card {W : Type*} [Fintype W] {H : SimpleGraph W}
    {v : W} {p : H.Walk v v} (hp : p.IsCycle) : p.length ≤ Fintype.card W := by
  have := hp.support_nodup.length_le_card
  simpa only [List.length_tail, Walk.length_support, Nat.add_sub_cancel] using this

/-- An odd cycle mapping into a graph has length at least that graph's girth.
The map need not be injective: its induced image is nonbipartite, hence contains
a cycle, whose length is at most the number of vertices in the image. -/
theorem girth_le_of_odd_cycle_hom {k : ℕ} [Fact (1 < k)]
    (hk : Odd k) (f : cyc k →g G) : G.egirth ≤ (k : ℕ∞) := by
  classical
  let I := Set.range f
  let : Fintype I := Fintype.ofFinite I
  let H := G.induce I
  let f' : cyc k →g H :=
    { toFun := Set.rangeFactorization f, map_rel' := fun h => f.map_adj h }
  have hnot : ¬ H.IsAcyclic := by
    intro ha
    exact cycle_not_bipartite hk (ha.colorable_two.of_hom f')
  obtain ⟨v, p, hp, _⟩ := exists_egirth_eq_length.mpr hnot
  have hsize : Fintype.card I ≤ k := by
    have h := Fintype.card_le_of_surjective (Set.rangeFactorization f)
      Set.rangeFactorization_surjective
    simpa only [ZMod.card] using h
  have hlen := (cycle_length_le_card hp).trans hsize
  have hp' := hp.map (f := (Embedding.induce (G := G) I).toHom) Subtype.val_injective
  exact hp'.egirth_le_length.trans (by simpa only [Walk.length_map, ENat.natCast_le_natCast] using hlen)

/-- If the source contains the target cycle and has no shorter cycle, the
target-free recognition problem is exactly homomorphism to that target. -/
theorem hasOddCycleCore_iff [Fact (1 < n)] (hn : 3 ≤ n) (hodd : Odd n)
    (hgirth : (n : ℕ∞) ≤ G.egirth) (hcontains : Nonempty (cyc n →g G)) :
    HasOddCycleCore G ↔ Nonempty (G →g cyc n) := by
  constructor
  · rintro ⟨k, hk, hkodd, ⟨f⟩, ⟨g⟩⟩
    let : Fact (1 < k) := ⟨by omega⟩
    obtain ⟨i⟩ := hcontains
    have hkn : k ≤ n := length_le_of_hom hodd (f.comp i)
    have hnk : n ≤ k := by
      exact_mod_cast hgirth.trans (girth_le_of_odd_cycle_hom hkodd g)
    have heq : k = n := by omega
    subst k
    exact ⟨f⟩
  · intro hf
    exact ⟨n, hn, hodd, hf, hcontains⟩

/-- For any graph with finite odd girth `n`, recognising an odd-cycle core is
exactly the question of mapping to its own shortest odd cycle. Even cycles of
smaller length are allowed. -/
theorem hasOddCycleCore_iff_of_oddGirth [Fact (1 < n)] (hg : oddGirth G = (n : ℕ∞)) :
    HasOddCycleCore G ↔ Nonempty (G →g cyc n) := by
  obtain ⟨a, w, hw, hoddw, hgw⟩ := exists_oddGirth_eq_length (G := G) (by simp [hg])
  have hlen : w.length = n := by exact_mod_cast hgw.symm.trans hg
  have hn : 3 ≤ n := hlen ▸ hw.three_le_length
  have hodd : Odd n := hlen ▸ hoddw
  let i : cyc n →g G := homOfClosedWalk w hlen
  constructor
  · rintro ⟨k, hk, hkodd, ⟨f⟩, ⟨g⟩⟩
    let : Fact (1 < k) := ⟨by omega⟩
    have hkn : k ≤ n := length_le_of_hom hodd (f.comp i)
    have hnk : n ≤ k := by
      have h := oddGirth_le_of_cycle_hom hkodd g
      rw [hg] at h
      exact_mod_cast h
    have he : k = n := by omega
    subst k
    exact ⟨f⟩
  · intro hf
    exact ⟨n, hn, hodd, hf, ⟨i⟩⟩

namespace ListReduction

/-- The same finite list-elimination construction recognises odd-cycle cores;
nonemptiness is the sole extra hypothesis needed to supply a reference cycle. -/
theorem source_hasOddCycleCore_iff {m : ℕ} [Fact (1 < n)]
    (F : SimpleGraph (Fin m)) (L : Fin m → Finset (ZMod n))
    (hodd : Odd n) (hn : 5 ≤ n) (hm : 0 < m) :
    HasOddCycleCore (source F L) ↔ Colorable F L := by
  rw [hasOddCycleCore_iff (by omega) hodd (source_le_egirth F L hn)
    ⟨(target_isContained F L (⟨0, hm⟩, 0)).some.toHom⟩]
  exact source_hom_iff_colorable F L hodd hn

end ListReduction
end TreewidthHom.OddCycle
