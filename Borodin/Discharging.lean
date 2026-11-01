/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Kotzig.Discharging
public import Borodin.Local

/-!
# Light triangular faces in plane maps of minimum degree five

Let `M` be a plane map of a finite simple graph of minimum degree at least five in which every
face of length three has weight (degree sum) at least `18`. Start from the charges of
`Kotzig.sum_charge` (total `-12 K < 0`) and move charge as follows:

* every face of length at least four gives `1/2` to each of its corners (`bigF`);
* every `7`-vertex gives `1/3` to each `5`-neighbour (`seven`);
* every vertex of degree at least eight gives `1/4` through each incident triangular face that
  has a `5`-vertex, split equally between the `5`-vertices of that face (`give`, `recv`).

Faces stay nonnegative (`face_orbit_nonneg`), `5`-vertices receive at least `1`
(`Borodin.one_le_sum_cv`), `7`-vertices have at least `2s - 7` corners between two consecutive
`5`-neighbours that are not on triangles, and vertices of degree at least eight lose at most
a quarter of their degree (`vertex_nonneg`). This is Borodin's discharging (as sketched by
Cranston and West), with face charges in place of the edge-maximal counterexample.
-/

@[expose] public section

namespace Borodin

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Kotzig

/-! ### Orbits of a permutation -/

section Orbit

variable {α : Type*} [Fintype α]

theorem card_cls_le_of_pow (π : Perm α) (y : α) {m : ℕ} (hm : 0 < m) (h : (π ^ m) y = y) :
    (cls (SameCycle.setoid π) y).card ≤ m := by
  classical
  have hsub : cls (SameCycle.setoid π) y ⊆ (Finset.range m).image (fun i => (π ^ i) y) := by
    intro z hz
    obtain ⟨n, hn⟩ := (mem_cls.1 hz).exists_nat_pow_eq
    refine Finset.mem_image.2 ⟨n % m, Finset.mem_range.2 (Nat.mod_lt _ hm), ?_⟩
    rw [← hn]
    conv_rhs => rw [← Nat.mod_add_div n m]
    rw [pow_add, Perm.mul_apply, pow_mul, Perm.pow_apply_eq_self_of_apply_eq_self h]
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

theorem pow_card_cls (π : Perm α) (y : α) :
    (π ^ (cls (SameCycle.setoid π) y).card) y = y := by
  obtain ⟨m, hm0, hm, hpow⟩ := exists_pow_eq_self π y
    (n := (cls (SameCycle.setoid π) y).card + 1) (by omega)
  have := card_cls_le_of_pow π y hm0 hpow
  have hm' : m = (cls (SameCycle.setoid π) y).card := by omega
  rw [← hm']
  exact hpow

end Orbit

/-! ### The rules -/

/-- What a vertex of degree `c` receives at a triangular corner whose other vertices have
degrees `a`, `b`. -/
noncomputable def rr (a c b : ℕ) : ℚ := if c = 5 then rv a b else 0

/-- What a vertex of degree `c` gives at a triangular corner whose other vertices have degrees
`a`, `b`. -/
noncomputable def gv (a c b : ℕ) : ℚ := if 8 ≤ c ∧ (a = 5 ∨ b = 5) then 1 / 4 else 0

/-- On every triangle, the vertices of degree at least eight give what the `5`-vertices
receive. -/
theorem tri_balance (A B C : ℕ) :
    0 ≤ (gv A C B + gv C B A + gv B A C) - (rr A C B + rr C B A + rr B A C) := by
  unfold gv rr rv
  split_ifs <;> first | (norm_num; done) | (exfalso; omega) | norm_num

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The `7`-vertex rule, along a dart from a `5`-vertex to a `7`-vertex. -/
noncomputable def seven (d : G.Dart) : ℚ :=
  if G.degree d.fst = 5 ∧ G.degree d.snd = 7 then 1 / 3 else 0

variable (M : PlaneMap G)

/-- A face of length at least four gives `1/2` to the corner at the head of `x`. -/
noncomputable def bigF (x : G.Dart) : ℚ := if 4 ≤ fLen M x then 1 / 2 else 0

/-- What the corner at the head of `x` receives from a triangular face. -/
noncomputable def recv (x : G.Dart) : ℚ :=
  if fLen M x = 3 then rr (G.degree x.fst) (G.degree x.snd) (G.degree (M.facePerm x).snd)
  else 0

/-- What the corner at the head of `x` gives to a triangular face. -/
noncomputable def give (x : G.Dart) : ℚ :=
  if fLen M x = 3 then gv (G.degree x.fst) (G.degree x.snd) (G.degree (M.facePerm x).snd)
  else 0

/-- No triangular face of weight at most `17`. -/
def NoLight : Prop :=
  ∀ x : G.Dart, fLen M x = 3 → 18 ≤ G.degree x.fst + G.degree x.snd + G.degree (M.facePerm x).snd

/-! ### Faces -/

theorem face_orbit_nonneg (hδ : ∀ v, 5 ≤ G.degree v) (x : G.Dart) :
    0 ≤ ∑ y ∈ cls (SameCycle.setoid M.facePerm) x,
      ((2 - 6 / (fLen M y : ℚ)) - bigF M y - recv M y + give M y) := by
  have hδ2 : ∀ v, 2 ≤ G.degree v := fun v => by have := hδ v; omega
  set O := cls (SameCycle.setoid M.facePerm) x with hO
  have hlen : ∀ y ∈ O, fLen M y = O.card := fun y hy => by
    unfold fLen
    rw [← cls_eq (mem_cls.1 hy)]
  have hℓ3 : 3 ≤ O.card := three_le_fLen M hδ2 x
  rcases Nat.lt_or_ge 3 O.card with h4 | h3
  · have hval : ∀ y ∈ O, ((2 - 6 / (fLen M y : ℚ)) - bigF M y - recv M y + give M y) =
        2 - 6 / (O.card : ℚ) - 1 / 2 := by
      intro y hy
      have hy4 : fLen M y = O.card := hlen y hy
      unfold bigF recv give
      rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), hy4]
      ring
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    have hpos : (0 : ℚ) < O.card := by exact_mod_cast (by omega : 0 < O.card)
    have h4' : (4 : ℚ) ≤ O.card := by exact_mod_cast h4
    have : (O.card : ℚ) * (2 - 6 / O.card - 1 / 2) = 3 / 2 * O.card - 6 := by
      field_simp
      ring
    rw [this]
    linarith
  · have hc3 : O.card = 3 := le_antisymm h3 hℓ3
    have h3x : (M.facePerm ^ 3) x = x := by
      have := pow_card_cls M.facePerm x
      rwa [← hO, hc3] at this
    have e3 : M.facePerm (M.facePerm (M.facePerm x)) = x := by simpa [pow_three] using h3x
    have n1 : M.facePerm x ≠ x := facePerm_ne_self M x
    have n2 : M.facePerm (M.facePerm x) ≠ x := facePerm_facePerm_ne M hδ2 x
    have n3 : M.facePerm (M.facePerm x) ≠ M.facePerm x := facePerm_ne_self M (M.facePerm x)
    have hOeq : ({x, M.facePerm x, M.facePerm (M.facePerm x)} : Finset G.Dart) = O := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact mem_cls.2 (SameCycle.refl _ _)
        · exact mem_cls.2 ⟨1, by simp⟩
        · exact mem_cls.2 ⟨2, by simp [pow_two]⟩
      · rw [hc3, Finset.card_eq_three.2 ⟨x, M.facePerm x, M.facePerm (M.facePerm x), n1.symm, n2.symm, n3.symm, rfl⟩]
    have hl : ∀ y ∈ O, fLen M y = 3 := fun y hy => (hlen y hy).trans hc3
    have mx : x ∈ O := hOeq ▸ by simp
    have m1 : M.facePerm x ∈ O := hOeq ▸ by simp
    have m2 : M.facePerm (M.facePerm x) ∈ O := hOeq ▸ by simp
    have hval : ∀ y ∈ O, ((2 - 6 / (fLen M y : ℚ)) - bigF M y - recv M y + give M y) =
        gv (G.degree y.fst) (G.degree y.snd) (G.degree (M.facePerm y).snd) -
          rr (G.degree y.fst) (G.degree y.snd) (G.degree (M.facePerm y).snd) := by
      intro y hy
      have hy3 := hl y hy
      unfold bigF recv give
      rw [if_neg (by omega), if_pos hy3, if_pos hy3, hy3]
      push_cast
      ring
    rw [Finset.sum_congr rfl hval, ← hOeq]
    rw [Finset.sum_insert (by simp [n1.symm, n2.symm]), Finset.sum_insert (by simp [n3.symm]),
      Finset.sum_singleton]
    have f1 : (M.facePerm x).fst = x.snd := fst_facePerm M x
    have f2 : (M.facePerm (M.facePerm x)).fst = (M.facePerm x).snd := fst_facePerm M (M.facePerm x)
    have f3 : (M.facePerm (M.facePerm x)).snd = x.fst := by
      have := fst_facePerm M (M.facePerm (M.facePerm x))
      rw [e3] at this
      exact this.symm
    rw [e3, f1, f2, f3]
    have := tri_balance (G.degree x.fst) (G.degree (M.facePerm x).snd) (G.degree x.snd)
    linarith

/-! ### The discharging preserves the total -/

theorem sum_split :
    ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + (2 - 6 / (fLen M d : ℚ))) =
      ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + seven d - seven d.symm + bigF M d.symm +
        recv M d.symm - give M d.symm) +
      ∑ x : G.Dart, ((2 - 6 / (fLen M x : ℚ)) - bigF M x - recv M x + give M x) := by
  have h1 : ∑ d : G.Dart, seven d.symm = ∑ d : G.Dart, seven d :=
    Equiv.sum_comp (dartSymm G) seven
  have h2 : ∑ d : G.Dart, bigF M d.symm = ∑ d : G.Dart, bigF M d :=
    Equiv.sum_comp (dartSymm G) (bigF M)
  have h3 : ∑ d : G.Dart, recv M d.symm = ∑ d : G.Dart, recv M d :=
    Equiv.sum_comp (dartSymm G) (recv M)
  have h4 : ∑ d : G.Dart, give M d.symm = ∑ d : G.Dart, give M d :=
    Equiv.sum_comp (dartSymm G) (give M)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2, h3, h4]
  ring

/-! ### Vertices -/

theorem fst_rot_pow (d : G.Dart) (n : ℕ) : ((M.rot ^ n) d).fst = d.fst :=
  ((sameCycle_rot_iff M).1 ⟨n, rfl⟩).symm

theorem vertex_nonneg (hδ : ∀ v, 5 ≤ G.degree v) (hno : NoLight M) (v : V) :
    0 ≤ ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v),
      ((1 - 6 / (G.degree d.fst : ℚ)) + seven d - seven d.symm + bigF M d.symm +
        recv M d.symm - give M d.symm) := by
  have hδ2 : ∀ v, 2 ≤ G.degree v := fun v => by have := hδ v; omega
  set F := Finset.univ.filter (fun d : G.Dart => d.fst = v) with hF
  have hFk : F.card = G.degree v := G.dart_fst_fiber_card_eq_degree v
  have hk5 : 5 ≤ G.degree v := hδ v
  have hkpos : (0 : ℚ) < G.degree v := by exact_mod_cast (by omega : 0 < G.degree v)
  have hmemF : ∀ d ∈ F, d.fst = v := fun d hd => (Finset.mem_filter.1 hd).2
  have hbig0 : ∀ d : G.Dart, 0 ≤ bigF M d := fun d => by unfold bigF; split_ifs <;> norm_num
  have hseven0 : ∀ d : G.Dart, 0 ≤ seven d := fun d => by unfold seven; split_ifs <;> norm_num
  -- the values at the darts of `v`
  have hS' : ∀ d ∈ F, seven d.symm =
      if G.degree d.snd = 5 ∧ G.degree v = 7 then 1 / 3 else 0 := by
    intro d hd
    unfold seven
    rw [show d.symm.snd = v from hmemF d hd]
    rfl
  have hR : ∀ d ∈ F, recv M d.symm = if fLen M d.symm = 3 then
      rr (G.degree d.snd) (G.degree v) (G.degree (M.rot d).snd) else 0 := by
    intro d hd
    unfold recv
    rw [show d.symm.snd = v from hmemF d hd, M.facePerm_apply, SimpleGraph.Dart.symm_symm]
    rfl
  have hG : ∀ d ∈ F, give M d.symm = if fLen M d.symm = 3 then
      gv (G.degree d.snd) (G.degree v) (G.degree (M.rot d).snd) else 0 := by
    intro d hd
    unfold give
    rw [show d.symm.snd = v from hmemF d hd, M.facePerm_apply, SimpleGraph.Dart.symm_symm]
    rfl
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hA : ∑ d ∈ F, (1 - 6 / (G.degree d.fst : ℚ)) = G.degree v - 6 := by
    rw [Finset.sum_congr rfl (fun d hd => show (1 - 6 / (G.degree d.fst : ℚ)) =
      1 - 6 / (G.degree v : ℚ) by rw [hmemF d hd]), Finset.sum_const, hFk, nsmul_eq_mul]
    field_simp
  rw [hA]
  have hRzero : G.degree v ≠ 5 → ∑ d ∈ F, recv M d.symm = 0 := fun h =>
    Finset.sum_eq_zero (fun d hd => by rw [hR d hd]; unfold rr; simp [h])
  have hGzero : G.degree v < 8 → ∑ d ∈ F, give M d.symm = 0 := fun h =>
    Finset.sum_eq_zero (fun d hd => by rw [hG d hd]; unfold gv; split_ifs <;> first | rfl | omega)
  have hS'zero : G.degree v ≠ 7 → ∑ d ∈ F, seven d.symm = 0 := fun h =>
    Finset.sum_eq_zero (fun d hd => by rw [hS' d hd]; simp [h])
  have hSzero : G.degree v ≠ 5 → ∑ d ∈ F, seven d = 0 := fun h =>
    Finset.sum_eq_zero (fun d hd => by unfold seven; rw [hmemF d hd]; simp [h])
  have hB0 : 0 ≤ ∑ d ∈ F, bigF M d.symm := Finset.sum_nonneg (fun d _ => hbig0 _)
  rcases (show G.degree v = 5 ∨ G.degree v = 6 ∨ G.degree v = 7 ∨ 8 ≤ G.degree v by omega)
    with h5 | h6 | h7 | h8
  · -- a `5`-vertex
    rw [hS'zero (by omega), hGzero (by omega)]
    obtain ⟨e0, he0⟩ : ∃ e0, e0 ∈ F := Finset.card_pos.1 (by omega)
    set e : ℕ → G.Dart := fun n => (M.rot ^ n) e0 with he
    have hcard : (cls (SameCycle.setoid M.rot) e0).card = 5 := by
      rw [card_cls_rot M e0, hmemF e0 he0, h5]
    have he5 : e 5 = e 0 := by
      have := pow_card_cls M.rot e0
      rw [hcard] at this
      simpa [he] using this
    have hesucc : ∀ n, e (n + 1) = M.rot (e n) := fun n => by
      simp only [he, pow_succ', Perm.mul_apply]
    have hemem : ∀ n, e n ∈ F := fun n => Finset.mem_filter.2
      ⟨Finset.mem_univ _, (fst_rot_pow M e0 n).trans (hmemF e0 he0)⟩
    have heinj : Set.InjOn e (Finset.range 5 : Set ℕ) := by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      by_contra hne
      have key : ∀ a b, a < b → b < 5 → e a = e b → False := by
        intro a b hab hb heq
        have hp : (M.rot ^ (b - a)) e0 = e0 := by
          apply (M.rot ^ a).injective
          rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
          exact heq.symm
        have := card_cls_le_of_pow M.rot e0 (by omega) hp
        omega
      rcases lt_or_gt_of_ne hne with h | h
      · exact key i j h hj hij
      · exact key j i h hi hij.symm
    have hFeq : (Finset.range 5).image e = F := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro z hz
        obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hz
        exact hemem n
      · rw [Finset.card_image_of_injOn heinj, hFk, h5]
        simp
    -- the value at each dart
    have hval : ∀ n, seven (e n) + bigF M (e n).symm + recv M (e n).symm =
        cv (G.degree (e n).snd) (G.degree (e (n + 1)).snd) (decide (fLen M (e n).symm = 3)) := by
      intro n
      have hd := hemem n
      rw [hR _ hd, hesucc]
      unfold seven bigF cv rr
      rw [hmemF _ hd, h5]
      have h3 := three_le_fLen M hδ2 (e n).symm
      by_cases ht : fLen M (e n).symm = 3
      · simp [ht]
      · have h4 : 4 ≤ fLen M (e n).symm := by omega
        simp [ht, h4]
    have hcorner : ∀ n, decide (fLen M (e n).symm = 3) = true →
        13 ≤ G.degree (e n).snd + G.degree (e (n + 1)).snd := by
      intro n ht
      have h := hno (e n).symm (of_decide_eq_true ht)
      rw [M.facePerm_apply, SimpleGraph.Dart.symm_symm, ← hesucc] at h
      have : (e n).symm.snd = v := hmemF _ (hemem n)
      change 18 ≤ G.degree (e n).snd + G.degree (e n).symm.snd + _ at h
      rw [this, h5] at h
      omega
    have hsum : ∑ d ∈ F, seven d + ∑ d ∈ F, bigF M d.symm + ∑ d ∈ F, recv M d.symm =
        ∑ n ∈ Finset.range 5, cv (G.degree (e n).snd) (G.degree (e (n + 1)).snd)
          (decide (fLen M (e n).symm = 3)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← hFeq,
        Finset.sum_image heinj]
      exact Finset.sum_congr rfl (fun n _ => hval n)
    have hlocal := one_le_sum_cv _ _ _ _ _ _ _ _ _ _ (hδ _) (hδ _) (hδ _) (hδ _) (hδ _)
      (hcorner 0) (hcorner 1) (hcorner 2) (hcorner 3) (by rw [← he5]; exact hcorner 4)
    simp only [zero_add, Nat.reduceAdd] at hlocal
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd] at hsum
    rw [he5] at hsum
    rw [h5] at hkpos ⊢
    push_cast
    linarith
  · -- a `6`-vertex
    rw [hS'zero (by omega), hRzero (by omega), hGzero (by omega), h6]
    have := Finset.sum_nonneg (fun d (_ : d ∈ F) => hseven0 d)
    push_cast
    linarith
  · -- a `7`-vertex
    rw [hSzero (by omega), hRzero (by omega), hGzero (by omega), h7]
    set S := F.filter (fun d => G.degree d.snd = 5) with hSdef
    have hS7 : ∑ d ∈ F, seven d.symm = (S.card : ℚ) / 3 := by
      rw [Finset.sum_congr rfl (fun d hd => hS' d hd), hSdef, Finset.card_filter]
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [h7]
      by_cases h : G.degree d.snd = 5 <;> simp [h]
    have hrotF : ∀ d ∈ F, M.rot d ∈ F := fun d hd =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, (M.isRotationSystem.fst_apply d).trans (hmemF d hd)⟩
    have hcount := card_add_card_le M.rot hrotF
      (Finset.filter_subset (fun d : G.Dart => G.degree d.snd = 5) F)
    rw [← hSdef, hFk, h7] at hcount
    have hbigS : ∀ d ∈ S.filter (fun d => M.rot d ∈ S), bigF M d.symm = 1 / 2 := by
      intro d hd
      have hd' := Finset.mem_filter.1 hd
      have hd1 := Finset.mem_filter.1 hd'.1
      have hd2 := Finset.mem_filter.1 hd'.2
      have h3 := three_le_fLen M hδ2 d.symm
      have hne : fLen M d.symm ≠ 3 := by
        intro ht
        have h := hno d.symm ht
        rw [M.facePerm_apply, SimpleGraph.Dart.symm_symm] at h
        change 18 ≤ G.degree d.snd + G.degree d.fst + G.degree (M.rot d).snd at h
        rw [hmemF d hd1.1, hd1.2, hd2.2, h7] at h
        omega
      unfold bigF
      rw [if_pos (by omega)]
    have hB : ((S.filter (fun d => M.rot d ∈ S)).card : ℚ) / 2 ≤ ∑ d ∈ F, bigF M d.symm := by
      have hsub : S.filter (fun d => M.rot d ∈ S) ⊆ F :=
        (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      calc ((S.filter (fun d => M.rot d ∈ S)).card : ℚ) / 2
          = ∑ d ∈ S.filter (fun d => M.rot d ∈ S), bigF M d.symm := by
            rw [Finset.sum_congr rfl hbigS, Finset.sum_const, nsmul_eq_mul]
            ring
        _ ≤ ∑ d ∈ F, bigF M d.symm :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hbig0 _)
    rw [hS7]
    have hc : ((S.card + S.card : ℕ) : ℚ) ≤ ((7 + (S.filter (fun d => M.rot d ∈ S)).card : ℕ) : ℚ) := by
      exact_mod_cast hcount
    push_cast at hc ⊢
    rcases Nat.lt_or_ge S.card 4 with hs | hs
    · have : (S.card : ℚ) ≤ 3 := by exact_mod_cast (by omega : S.card ≤ 3)
      have : (0 : ℚ) ≤ ((S.filter (fun d => M.rot d ∈ S)).card : ℚ) := Nat.cast_nonneg _
      linarith
    · have : (4 : ℚ) ≤ S.card := by exact_mod_cast hs
      linarith
  · -- a vertex of degree at least eight
    rw [hS'zero (by omega), hRzero (by omega), hSzero (by omega)]
    have hGle : ∑ d ∈ F, give M d.symm ≤ F.card • (1 / 4 : ℚ) :=
      Finset.sum_le_card_nsmul F _ _ (fun d hd => by
        rw [hG d hd]; unfold gv; split_ifs <;> norm_num)
    rw [hFk, nsmul_eq_mul] at hGle
    have h8' : (8 : ℚ) ≤ G.degree v := by exact_mod_cast h8
    linarith

/-! ### The light triangular face -/

theorem exists_light_face [Nonempty V] (hδ : ∀ v, 5 ≤ G.degree v) :
    ∃ x : G.Dart, fLen M x = 3 ∧
      G.degree x.fst + G.degree x.snd + G.degree (M.facePerm x).snd ≤ 17 := by
  by_contra hcon
  push Not at hcon
  have hno : NoLight M := fun x hx => by have := hcon x hx; omega
  obtain ⟨v0⟩ := ‹Nonempty V›
  obtain ⟨u, hu⟩ : ∃ u, G.Adj v0 u := by
    have hpos : 0 < (G.neighborFinset v0).card := by
      rw [G.card_neighborFinset_eq_degree]
      have := hδ v0
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.1 hpos
    exact ⟨u, by simpa using hu⟩
  have hK : (1 : ℚ) ≤ numComponents M.rot (dartSymm G) := by
    exact_mod_cast one_le_numComponents M ⟨(v0, u), hu⟩
  have hsum := sum_charge M
  rw [sum_split M] at hsum
  have hV : 0 ≤ ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + seven d - seven d.symm +
      bigF M d.symm + recv M d.symm - give M d.symm) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun d : G.Dart => d.fst)]
    exact Finset.sum_nonneg (fun v _ => vertex_nonneg M hδ hno v)
  have hFc : 0 ≤ ∑ x : G.Dart, ((2 - 6 / (fLen M x : ℚ)) - bigF M x - recv M x + give M x) := by
    rw [← sum_avg_cls (SameCycle.setoid M.facePerm)]
    exact Finset.sum_nonneg (fun x _ => div_nonneg (face_orbit_nonneg M hδ x) (Nat.cast_nonneg _))
  linarith

end Borodin
