/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Disjoint
public import Mathlib.SetTheory.Cardinal.Finite
import MinimalProlific
import Mathlib.Tactic

@[expose] public section

namespace MinimalProlificChallenge

/-- Taxicab (`L₁`) distance between two lattice points in `ℤ × ℤ`. -/
def taxicabDist (p q : ℤ × ℤ) : ℤ := |p.1 - q.1| + |p.2 - q.2|

/-- Radius-`m` Lee sphere centered at `p ∈ ℤ × ℤ`. -/
def leeSphere (m : ℕ) (p : ℤ × ℤ) : Set (ℤ × ℤ) :=
  { q | taxicabDist p q ≤ (m : ℤ) }

/-- A permutation `w : Equiv.Perm (Fin n)` has taxicab breadth at least `d` iff every two
distinct plot points `(i + 1, w(i) + 1)` and `(j + 1, w(j) + 1)` lie at `L₁` distance at
least `d`. -/
def HasBreadthAtLeast {n : ℕ} (d : ℕ) (w : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    (d : ℤ) ≤ taxicabDist ((i.val : ℤ) + 1, ((w i).val : ℤ) + 1)
      ((j.val : ℤ) + 1, ((w j).val : ℤ) + 1)

/-- The positive modular linear permutation `w(i) + 1 ≡ +(2m + 1)(i + 1) (mod 2m^2 + 2m + 1)`. -/
def IsSigmaPlus (m : ℕ) (w : Equiv.Perm (Fin (2 * m ^ 2 + 2 * m))) : Prop :=
  ∀ i : Fin (2 * m ^ 2 + 2 * m),
    ((w i).val : ℤ) + 1 ≡
      ((2 * m + 1 : ℕ) : ℤ) * ((i.val : ℤ) + 1) [ZMOD ((2 * m ^ 2 + 2 * m + 1 : ℕ) : ℤ)]

/-- The negative modular linear permutation `w(i) + 1 ≡ -(2m + 1)(i + 1) (mod 2m^2 + 2m + 1)`. -/
def IsSigmaMinus (m : ℕ) (w : Equiv.Perm (Fin (2 * m ^ 2 + 2 * m))) : Prop :=
  ∀ i : Fin (2 * m ^ 2 + 2 * m),
    ((w i).val : ℤ) + 1 ≡
      -(((2 * m + 1 : ℕ) : ℤ) * ((i.val : ℤ) + 1)) [ZMOD ((2 * m ^ 2 + 2 * m + 1 : ℕ) : ℤ)]

/-- Reverse of a permutation on `Fin n`. -/
def permReverse {n : ℕ} (w : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans w

/-- Complement of a permutation on `Fin n`. -/
def permComplement {n : ℕ} (w : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  w.trans Fin.revPerm

/-- Inverse of a permutation on `Fin n`. -/
def permInverse {n : ℕ} (w : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  w.symm

/-- 90-degree rotation of a permutation on `Fin n`. -/
def permRot90 {n : ℕ} (w : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans w.symm

/-- A set `T ⊆ ℤ × ℤ` is a radius-`m` Lee-sphere tiling of `ℤ^2` iff the radius-`m` Lee
spheres centered at points of `T` are pairwise disjoint and cover all of `ℤ × ℤ`. -/
def IsLeeTiling (m : ℕ) (T : Set (ℤ × ℤ)) : Prop :=
  (∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → Disjoint (leeSphere m c) (leeSphere m c')) ∧
  (∀ z : ℤ × ℤ, ∃ c ∈ T, z ∈ leeSphere m c)

/-- Standard Lee-tiling lattice `Λ⁺ = ℤ(m + 1, m) + ℤ(-m, m + 1)`. -/
def LambdaPlus (m : ℕ) : Set (ℤ × ℤ) :=
  { z | ∃ i j : ℤ, z = (i * ((m : ℤ) + 1) - j * (m : ℤ), i * (m : ℤ) + j * ((m : ℤ) + 1)) }

/-- Mirror Lee-tiling lattice `Λ⁻ = {(-x, y) | (x, y) ∈ Λ⁺}`. -/
def LambdaMinus (m : ℕ) : Set (ℤ × ℤ) :=
  { z | ∃ i j : ℤ, z = (-(i * ((m : ℤ) + 1) - j * (m : ℤ)), i * (m : ℤ) + j * ((m : ℤ) + 1)) }

private theorem perm_eq_of_modEq {m : ℕ}
    (u v : Equiv.Perm (Fin (MinimalProlific.n_odd m)))
    (h : ∀ i : Fin (MinimalProlific.n_odd m),
      ((u i).val : ℤ) + 1 ≡ ((v i).val : ℤ) + 1 [ZMOD (MinimalProlific.N_odd m : ℤ)]) :
    u = v := by
  ext i
  have hN1 : (MinimalProlific.N_odd m : ℤ) = (MinimalProlific.n_odd m : ℤ) + 1 := by
    exact_mod_cast (MinimalProlific.n_odd_add_one m).symm
  have hb1 : 0 ≤ ((u i).val : ℤ) + 1 ∧ ((u i).val : ℤ) + 1 < (MinimalProlific.N_odd m : ℤ) := by
    have := (u i).isLt; omega
  have hb2 : 0 ≤ ((v i).val : ℤ) + 1 ∧ ((v i).val : ℤ) + 1 < (MinimalProlific.N_odd m : ℤ) := by
    have := (v i).isLt; omega
  have hi := h i
  rw [Int.ModEq, Int.emod_eq_of_lt hb1.1 hb1.2, Int.emod_eq_of_lt hb2.1 hb2.2] at hi
  omega

private theorem isSigmaPlus_iff {m : ℕ} (hm : 1 ≤ m)
    (w : Equiv.Perm (Fin (2 * m ^ 2 + 2 * m))) :
    IsSigmaPlus m w ↔ w = MinimalProlific.sigmaPlus m := by
  constructor
  · intro hw
    apply perm_eq_of_modEq
    intro i
    exact (hw i).trans (MinimalProlific.sigmaPlus_mod_eq hm i).symm
  · rintro rfl i
    exact MinimalProlific.sigmaPlus_mod_eq hm i

private theorem isSigmaMinus_iff {m : ℕ} (hm : 1 ≤ m)
    (w : Equiv.Perm (Fin (2 * m ^ 2 + 2 * m))) :
    IsSigmaMinus m w ↔ w = MinimalProlific.sigmaMinus m := by
  constructor
  · intro hw
    apply perm_eq_of_modEq
    intro i
    exact (hw i).trans (MinimalProlific.sigmaMinus_mod_eq hm i).symm
  · rintro rfl i
    exact MinimalProlific.sigmaMinus_mod_eq hm i

theorem odd_minimal_prolific_classification (m : ℕ) (hm : 1 ≤ m)
    (w : Equiv.Perm (Fin (2 * m ^ 2 + 2 * m))) :
    HasBreadthAtLeast (2 * m + 1) w ↔ IsSigmaPlus m w ∨ IsSigmaMinus m w := by
  rw [isSigmaPlus_iff hm w, isSigmaMinus_iff hm w]
  exact MinimalProlific.odd_minimal_prolific_classification m hm w

theorem odd_minimal_prolific_card_eq_two (m : ℕ) (hm : 1 ≤ m) :
    Nat.card { w : Equiv.Perm (Fin (2 * m ^ 2 + 2 * m)) //
      HasBreadthAtLeast (2 * m + 1) w } = 2 := by
  let _ : DecidablePred (HasBreadthAtLeast (n := 2 * m ^ 2 + 2 * m) (2 * m + 1)) :=
    MinimalProlific.instDecidablePredIsValidOdd m
  rw [Nat.card_eq_fintype_card]
  exact MinimalProlific.odd_minimal_prolific_card_eq_two m hm

theorem odd_minimal_prolific_dihedral_orbit (m : ℕ) (hm : 1 ≤ m) :
    ∃ w₁ w₂ : Equiv.Perm (Fin (2 * m ^ 2 + 2 * m)),
      IsSigmaPlus m w₁ ∧ IsSigmaMinus m w₂ ∧ w₁ ≠ w₂ ∧
      permReverse w₁ = w₂ ∧ permComplement w₁ = w₂ ∧ permInverse w₁ = w₂ ∧
      permRot90 w₁ = w₁ ∧ permRot90 w₂ = w₂ := by
  rcases MinimalProlific.odd_symmetries_single_orbit m hm with
    ⟨hne, hrev, hcomp, hinv, hrot1, hrot2, -, -⟩
  exact ⟨MinimalProlific.sigmaPlus m, MinimalProlific.sigmaMinus m,
    (isSigmaPlus_iff hm _).mpr rfl, (isSigmaMinus_iff hm _).mpr rfl,
    hne, hrev, hcomp, hinv, hrot1, hrot2⟩

theorem lee_tiling_classification (m : ℕ) (hm : 1 ≤ m) (T : Set (ℤ × ℤ))
    (hT : IsLeeTiling m T) (hO : (0, 0) ∈ T) :
    T = LambdaPlus m ∨ T = LambdaMinus m :=
  MinimalProlific.lee_tiling_classification m hm T hT hO

theorem even_strip_lower_bound (r : ℕ) (hr : 2 ≤ r) :
    2 * Nat.factorial (r - 1) ≤
      Nat.card { w : Equiv.Perm (Fin (2 * r ^ 2 - 1)) //
        HasBreadthAtLeast (2 * r) w } := by
  let _ : DecidablePred (HasBreadthAtLeast (n := 2 * r ^ 2 - 1) (2 * r)) :=
    MinimalProlific.instDecidablePredIsValidEven r
  rw [Nat.card_eq_fintype_card]
  exact MinimalProlific.even_strip_lower_bound r hr

end MinimalProlificChallenge
