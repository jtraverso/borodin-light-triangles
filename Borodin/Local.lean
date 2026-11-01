/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# The charge received by a `5`-vertex

Around a `5`-vertex `v` with neighbours of degrees `d₀, …, d₄` in rotation order, the corner
between the `i`-th and the `(i+1)`-st neighbour is either on a face of length at least four,
which gives `1/2`, or on a triangle, through which every neighbour of degree at least eight
gives `1/4`, split equally between the `5`-vertices of the triangle (`rv`); every neighbour of
degree seven gives `1/3`. If no triangle at `v` has weight below `18`, then `v` receives at
least `1` (`one_le_sum_cv`). The finite case analysis (degrees capped at eight) is checked by
`decide` (`local_check`).
-/

@[expose] public section

namespace Borodin

/-- The charge a `5`-vertex receives through a triangle whose other two vertices have degrees
`a` and `b`. -/
noncomputable def rv (a b : ℕ) : ℚ :=
  (if 8 ≤ a then (if b = 5 then 1 / 8 else 1 / 4) else 0) +
    (if 8 ≤ b then (if a = 5 then 1 / 8 else 1 / 4) else 0)

/-- The charge a `5`-vertex receives at the corner between neighbours of degrees `a` and `b`
(on a triangle if `t`), together with the share `1/3` of the first neighbour if it has degree
seven. -/
noncomputable def cv (a b : ℕ) (t : Bool) : ℚ :=
  (if a = 7 then 1 / 3 else 0) + (if t then rv a b else 1 / 2)

/-- `24 * cv`, in natural numbers. -/
def c24 (a b : ℕ) (t : Bool) : ℕ :=
  (if a = 7 then 8 else 0) +
    (if t then (if 8 ≤ a then (if b = 5 then 3 else 6) else 0) +
      (if 8 ≤ b then (if a = 5 then 3 else 6) else 0) else 12)

/-- Degrees capped at eight. -/
def cap (a : ℕ) : ℕ := if 8 ≤ a then 8 else a

set_option maxRecDepth 100000 in
theorem local_check : ∀ x0 x1 x2 x3 x4 : Fin 4, ∀ t0 t1 t2 t3 t4 : Bool,
    (t0 = true → 13 ≤ (x0.val + 5) + (x1.val + 5)) →
    (t1 = true → 13 ≤ (x1.val + 5) + (x2.val + 5)) →
    (t2 = true → 13 ≤ (x2.val + 5) + (x3.val + 5)) →
    (t3 = true → 13 ≤ (x3.val + 5) + (x4.val + 5)) →
    (t4 = true → 13 ≤ (x4.val + 5) + (x0.val + 5)) →
    24 ≤ c24 (x0.val + 5) (x1.val + 5) t0 + c24 (x1.val + 5) (x2.val + 5) t1 +
      c24 (x2.val + 5) (x3.val + 5) t2 + c24 (x3.val + 5) (x4.val + 5) t3 +
      c24 (x4.val + 5) (x0.val + 5) t4 := by
  decide

theorem cv_eq (a b : ℕ) (t : Bool) : cv a b t = (c24 a b t : ℚ) / 24 := by
  unfold cv c24 rv
  split_ifs <;> push_cast <;> norm_num

theorem c24_cap {a b : ℕ} (t : Bool) (ha : 5 ≤ a) (hb : 5 ≤ b) :
    c24 (cap a) (cap b) t = c24 a b t := by
  unfold c24 cap
  split_ifs <;> omega

theorem toFin (a : ℕ) (ha : 5 ≤ a) : ∃ x : Fin 4, x.val + 5 = cap a :=
  ⟨⟨cap a - 5, by unfold cap; split_ifs <;> omega⟩, by unfold cap; split_ifs <;> simp <;> omega⟩

theorem cap_add {a b : ℕ} (ha : 5 ≤ a) (hb : 5 ≤ b) (h : 13 ≤ a + b) : 13 ≤ cap a + cap b := by
  unfold cap
  split_ifs <;> omega

/-- A `5`-vertex receives at least `1`. -/
theorem one_le_sum_cv (d0 d1 d2 d3 d4 : ℕ) (t0 t1 t2 t3 t4 : Bool) (h0 : 5 ≤ d0) (h1 : 5 ≤ d1)
    (h2 : 5 ≤ d2) (h3 : 5 ≤ d3) (h4 : 5 ≤ d4)
    (k0 : t0 = true → 13 ≤ d0 + d1) (k1 : t1 = true → 13 ≤ d1 + d2)
    (k2 : t2 = true → 13 ≤ d2 + d3) (k3 : t3 = true → 13 ≤ d3 + d4)
    (k4 : t4 = true → 13 ≤ d4 + d0) :
    1 ≤ cv d0 d1 t0 + cv d1 d2 t1 + cv d2 d3 t2 + cv d3 d4 t3 + cv d4 d0 t4 := by
  obtain ⟨x0, e0⟩ := toFin d0 h0
  obtain ⟨x1, e1⟩ := toFin d1 h1
  obtain ⟨x2, e2⟩ := toFin d2 h2
  obtain ⟨x3, e3⟩ := toFin d3 h3
  obtain ⟨x4, e4⟩ := toFin d4 h4
  have key := local_check x0 x1 x2 x3 x4 t0 t1 t2 t3 t4
    (fun h => by rw [e0, e1]; exact cap_add h0 h1 (k0 h))
    (fun h => by rw [e1, e2]; exact cap_add h1 h2 (k1 h))
    (fun h => by rw [e2, e3]; exact cap_add h2 h3 (k2 h))
    (fun h => by rw [e3, e4]; exact cap_add h3 h4 (k3 h))
    (fun h => by rw [e4, e0]; exact cap_add h4 h0 (k4 h))
  rw [e0, e1, e2, e3, e4, c24_cap t0 h0 h1, c24_cap t1 h1 h2, c24_cap t2 h2 h3,
    c24_cap t3 h3 h4, c24_cap t4 h4 h0] at key
  rw [cv_eq, cv_eq, cv_eq, cv_eq, cv_eq]
  have : ((24 : ℕ) : ℚ) ≤ ((c24 d0 d1 t0 + c24 d1 d2 t1 + c24 d2 d3 t2 + c24 d3 d4 t3 +
      c24 d4 d0 t4 : ℕ) : ℚ) := by exact_mod_cast key
  push_cast at this
  linarith

end Borodin
