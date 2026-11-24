module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Disjoint
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Palomar Challenge: Minimal `k`-Prolific Permutations for Every Odd `k`

Self-contained definitions and compared headline theorems for:
1. `odd_minimal_prolific_classification`: For every odd `k = 2m - 1` (`m ≥ 1`), at minimal
   size `n = 2m^2 + 2m`, modulus `N = 2m^2 + 2m + 1`, and taxicab breadth threshold
   `d = k + 2 = 2m + 1`, a permutation `w : Equiv.Perm (Fin n)` has taxicab breadth at least `d`
   iff for all `i`, `w(i) + 1 ≡ +(2m + 1)(i + 1) (mod N)` or for all `i`,
   `w(i) + 1 ≡ -(2m + 1)(i + 1) (mod N)`. Combined with Bevan, Homberger, and Tenner's
   breadth criterion (Theorem 2.25) and minimal-size formula (Corollary 4.3), this settles
   Conjecture 5.1 of Bevan, Homberger, and Tenner (2018) for every odd `k`.
2. `odd_minimal_prolific_card_eq_two`: Exactly two permutations of `Fin (2m^2 + 2m)` have
   taxicab breadth at least `2m + 1`.
3. `odd_minimal_prolific_dihedral_orbit`: Those two valid permutations are distinct, mutually
   related by reverse, complement, and inverse, and fixed by 90-degree rotation (forming a
   single `D₄` symmetry orbit of size `2`).
4. `lee_tiling_classification`: Every radius-`m` Lee-sphere tiling `T ⊆ ℤ × ℤ` containing
   `(0, 0)` equals `LambdaPlus m` or `LambdaMinus m`.
5. `even_strip_lower_bound`: For every even `k = 2r - 2` (`r ≥ 2`), at minimal size
   `n = 2r^2 - 1` and breadth threshold `d = 2r`, at least `2 * (r - 1)!` permutations of
   `Fin n` have taxicab breadth at least `2r`.
-/

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

/-- **Theorem 1 (Classification for Every Odd `k = 2m - 1`):**
For every `m ≥ 1`, a permutation `w` of `Fin (2m^2 + 2m)` has taxicab breadth at least `2m + 1`
iff `w` satisfies the positive or negative modular linear congruence modulo `2m^2 + 2m + 1`. -/
theorem odd_minimal_prolific_classification (m : ℕ) (hm : 1 ≤ m)
    (w : Equiv.Perm (Fin (2 * m ^ 2 + 2 * m))) :
    HasBreadthAtLeast (2 * m + 1) w ↔ IsSigmaPlus m w ∨ IsSigmaMinus m w := by
  sorry

/-- **Theorem 1 (Exact Count = 2):**
For every `m ≥ 1` (`k = 2m - 1`), exactly two permutations of `Fin (2m^2 + 2m)` have taxicab
breadth at least `2m + 1`. -/
theorem odd_minimal_prolific_card_eq_two (m : ℕ) (hm : 1 ≤ m) :
    Nat.card { w : Equiv.Perm (Fin (2 * m ^ 2 + 2 * m)) //
      HasBreadthAtLeast (2 * m + 1) w } = 2 := by
  sorry

/-- **Theorem 1 (Single `D₄` Dihedral Orbit):**
For every `m ≥ 1`, the two modular linear minimizers are distinct, mutually related by
reverse, complement, and inverse, and fixed by 90-degree rotation. -/
theorem odd_minimal_prolific_dihedral_orbit (m : ℕ) (hm : 1 ≤ m) :
    ∃ w₁ w₂ : Equiv.Perm (Fin (2 * m ^ 2 + 2 * m)),
      IsSigmaPlus m w₁ ∧ IsSigmaMinus m w₂ ∧ w₁ ≠ w₂ ∧
      permReverse w₁ = w₂ ∧ permComplement w₁ = w₂ ∧ permInverse w₁ = w₂ ∧
      permRot90 w₁ = w₁ ∧ permRot90 w₂ = w₂ := by
  sorry

/-- **Lemma 1 (2D Radius-`m` Lee-Sphere Tiling Rigidity):**
For every `m ≥ 1`, every radius-`m` Lee-sphere tiling `T ⊆ ℤ × ℤ` containing `(0, 0)` equals
`LambdaPlus m` or `LambdaMinus m`. -/
theorem lee_tiling_classification (m : ℕ) (hm : 1 ≤ m) (T : Set (ℤ × ℤ))
    (hT : IsLeeTiling m T) (hO : (0, 0) ∈ T) :
    T = LambdaPlus m ∨ T = LambdaMinus m := by
  sorry

/-- **Theorem 2 (Even-`k` Factorial Lower Bound):**
For every `r ≥ 2` (even `k = 2r - 2`, minimal size `n = 2r^2 - 1`), at least `2 * (r - 1)!`
permutations of `Fin (2r^2 - 1)` have taxicab breadth at least `2r`. -/
theorem even_strip_lower_bound (r : ℕ) (hr : 2 ≤ r) :
    2 * Nat.factorial (r - 1) ≤
      Nat.card { w : Equiv.Perm (Fin (2 * r ^ 2 - 1)) //
        HasBreadthAtLeast (2 * r) w } := by
  sorry

end MinimalProlificChallenge
