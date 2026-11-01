/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Borodin.Discharging

/-!
# Borodin's light triangle

* `light_face`: every plane map of a finite simple graph of minimum degree at least five has a
  face of length three whose vertices have degree sum at most `17`;
* `light_triangle`: a finite simple planar graph of minimum degree at least five has a triangle
  of weight at most `17`.
-/

@[expose] public section

namespace Borodin

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Kotzig

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem light_face [Nonempty V] (M : PlaneMap G) (hδ : ∀ v, 5 ≤ G.degree v) :
    ∃ d : G.Dart, ((M.rot * dartSymm G) ^ 3) d = d ∧
      G.degree d.fst + G.degree ((M.rot * dartSymm G) d).fst +
        G.degree (((M.rot * dartSymm G) ^ 2) d).fst ≤ 17 := by
  classical
  obtain ⟨x, hx3, hx⟩ := exists_light_face M hδ
  refine ⟨x, ?_, ?_⟩
  · have := pow_card_cls M.facePerm x
    unfold fLen at hx3
    rw [hx3] at this
    exact this
  · have h1 : (M.facePerm x).fst = x.snd := fst_facePerm M x
    have h2 : (M.facePerm (M.facePerm x)).fst = (M.facePerm x).snd := fst_facePerm M _
    change G.degree x.fst + G.degree (M.facePerm x).fst +
      G.degree ((M.facePerm ^ 2) x).fst ≤ 17
    rw [pow_two, Perm.mul_apply, h2, h1]
    exact hx

theorem light_triangle [Nonempty V] (hG : IsPlanar G) (hδ : ∀ v, 5 ≤ G.degree v) :
    ∃ u v w, G.Adj u v ∧ G.Adj v w ∧ G.Adj w u ∧ G.degree u + G.degree v + G.degree w ≤ 17 := by
  classical
  obtain ⟨M⟩ := hG
  obtain ⟨x, hx3, hx⟩ := exists_light_face M hδ
  have h3 : M.facePerm (M.facePerm (M.facePerm x)) = x := by
    have := pow_card_cls M.facePerm x
    unfold fLen at hx3
    rw [hx3] at this
    simpa [pow_three] using this
  have h1 : (M.facePerm x).fst = x.snd := fst_facePerm M x
  have h2 : (M.facePerm (M.facePerm x)).fst = (M.facePerm x).snd := fst_facePerm M _
  have h4 : (M.facePerm (M.facePerm x)).snd = x.fst := by
    have := fst_facePerm M (M.facePerm (M.facePerm x))
    rw [h3] at this
    exact this.symm
  refine ⟨x.fst, x.snd, (M.facePerm x).snd, x.adj, ?_, ?_, hx⟩
  · have := (M.facePerm x).adj
    rwa [h1] at this
  · have := (M.facePerm (M.facePerm x)).adj
    rwa [h2, h4] at this

end Borodin
