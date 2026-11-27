/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq

import Mathlib.Tactic

/-!
# Core Definitions for `MinimalProlific` (Bevan–Homberger–Tenner Conjecture 5.1 & Claim B1)

1. Taxicab norm and distance on `ℤ × ℤ`, Lee spheres `leeSphere m p` and finite representations
   `leeSphereFinset m p`, vertical chords `sphereColFinset m p x`, and exact cardinality `N_odd m`.
2. Parameters for odd `k = 2m - 1`: `N_odd m = 2m^2 + 2m + 1`, `n_odd m = 2m^2 + 2m`,
   `d_odd m = 2m + 1`.
3. Valid permutations `IsValidPerm d w` (`Equiv.Perm (Fin n)` whose 1-indexed plot points in
   `[1, n]^2` have pairwise taxicab distance `≥ d`), `IsValidOdd m w`, covered cells, and holes.
4. Explicit odd minimizers `sigmaPlus m` (`d * i mod N`) and `sigmaMinus m` (`-d * i mod N`).
5. The eight symmetries of the square (`D₄`) acting equivariantly on `ℤ × ℤ` and
   `Equiv.Perm (Fin n)`, preserving validity and permuting covered cells and holes.
-/

@[expose] public section

namespace MinimalProlific

open Finset

/-! ## Section 1: Taxicab Distance and Lee Spheres -/

/-- Taxicab (L₁) norm on `ℤ × ℤ`. -/
def taxicabNorm (z : ℤ × ℤ) : ℤ := |z.1| + |z.2|

/-- Taxicab (L₁) distance between two lattice points in `ℤ × ℤ`. -/
def taxicabDist (p q : ℤ × ℤ) : ℤ := |p.1 - q.1| + |p.2 - q.2|

/-- Radius-`m` Lee sphere centered at `p ∈ ℤ × ℤ`. -/
def leeSphere (m : ℕ) (p : ℤ × ℤ) : Set (ℤ × ℤ) :=
  { q | taxicabDist p q ≤ (m : ℤ) }

theorem taxicabNorm_nonneg (z : ℤ × ℤ) : 0 ≤ taxicabNorm z := by
  unfold taxicabNorm; positivity

theorem taxicabDist_nonneg (p q : ℤ × ℤ) : 0 ≤ taxicabDist p q := by
  unfold taxicabDist; positivity

theorem taxicabDist_self (p : ℤ × ℤ) : taxicabDist p p = 0 := by
  simp [taxicabDist]

theorem taxicabDist_comm (p q : ℤ × ℤ) : taxicabDist p q = taxicabDist q p := by
  simp only [taxicabDist, abs_sub_comm]

theorem taxicabDist_eq_zero {p q : ℤ × ℤ} : taxicabDist p q = 0 ↔ p = q := by
  constructor
  · intro h
    have h1 : |p.1 - q.1| + |p.2 - q.2| = 0 := h
    have hxa : |p.1 - q.1| = 0 := by linarith [abs_nonneg (p.1 - q.1), abs_nonneg (p.2 - q.2)]
    have hya : |p.2 - q.2| = 0 := by linarith [abs_nonneg (p.1 - q.1), abs_nonneg (p.2 - q.2)]
    exact Prod.ext (sub_eq_zero.mp (abs_eq_zero.mp hxa)) (sub_eq_zero.mp (abs_eq_zero.mp hya))
  · rintro rfl; exact taxicabDist_self p

theorem taxicabDist_triangle (p q r : ℤ × ℤ) :
    taxicabDist p r ≤ taxicabDist p q + taxicabDist q r := by
  unfold taxicabDist
  linarith [abs_sub_le p.1 q.1 r.1, abs_sub_le p.2 q.2 r.2]

theorem taxicabDist_translate (p q v : ℤ × ℤ) :
    taxicabDist (p.1 + v.1, p.2 + v.2) (q.1 + v.1, q.2 + v.2) = taxicabDist p q := by
  unfold taxicabDist
  ring_nf

theorem taxicabDist_ge_abs_sum (p q : ℤ × ℤ) :
    |(p.1 - q.1) + (p.2 - q.2)| ≤ taxicabDist p q := by
  unfold taxicabDist
  exact abs_add_le (p.1 - q.1) (p.2 - q.2)

theorem taxicabDist_ge_abs_diff (p q : ℤ × ℤ) :
    |(p.1 - q.1) - (p.2 - q.2)| ≤ taxicabDist p q := by
  unfold taxicabDist
  exact (abs_sub_le (p.1 - q.1) 0 (p.2 - q.2)).trans_eq (by simp [abs_sub_comm])

/-- Finite set of `y`-coordinates in column `x` belonging to `leeSphere m p`. -/
def sphereColFinset (m : ℕ) (p : ℤ × ℤ) (x : ℤ) : Finset ℤ :=
  if |x - p.1| ≤ (m : ℤ) then
    Finset.Icc (p.2 - ((m : ℤ) - |x - p.1|)) (p.2 + ((m : ℤ) - |x - p.1|))
  else ∅

theorem mem_sphereColFinset {m : ℕ} {p : ℤ × ℤ} {x y : ℤ} :
    y ∈ sphereColFinset m p x ↔ (x, y) ∈ leeSphere m p := by
  unfold sphereColFinset leeSphere taxicabDist
  change _ ↔ |p.1 - x| + |p.2 - y| ≤ (m : ℤ)
  rw [abs_sub_comm p.1 x]
  split_ifs with hx
  · rw [Finset.mem_Icc, abs_sub_comm p.2 y]
    constructor
    · intro ⟨h1, h2⟩
      have ha : |y - p.2| ≤ (m : ℤ) - |x - p.1| := abs_le.mpr ⟨by omega, by omega⟩
      omega
    · intro h
      have ha : |y - p.2| ≤ (m : ℤ) - |x - p.1| := by omega
      rcases abs_le.mp ha with ⟨h1, h2⟩
      exact ⟨by omega, by omega⟩
  · simp only [Finset.notMem_empty, false_iff]
    have hnonneg : 0 ≤ |p.2 - y| := abs_nonneg _
    omega

theorem card_sphereColFinset (m : ℕ) (p : ℤ × ℤ) (x : ℤ) :
    (sphereColFinset m p x).card =
      if (x - p.1).natAbs ≤ m then 2 * (m - (x - p.1).natAbs) + 1 else 0 := by
  unfold sphereColFinset
  have hab : |x - p.1| = ((x - p.1).natAbs : ℤ) := Int.abs_eq_natAbs _
  split_ifs with h1 h2 h2
  · rw [Int.card_Icc]
    have h1' : ((x - p.1).natAbs : ℤ) ≤ (m : ℤ) := hab ▸ h1
    omega
  · exfalso; apply h2; rw [hab] at h1; exact_mod_cast h1
  · exfalso; apply h1; rw [hab]; exact_mod_cast h2
  · simp

/-- Finite set of lattice points in `leeSphere m p`. -/
def leeSphereFinset (m : ℕ) (p : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (p.1 - (m : ℤ)) (p.1 + (m : ℤ))) ×ˢ
    (Finset.Icc (p.2 - (m : ℤ)) (p.2 + (m : ℤ)))).filter
    (fun q => taxicabDist p q ≤ (m : ℤ))

theorem mem_leeSphereFinset {m : ℕ} {p q : ℤ × ℤ} :
    q ∈ leeSphereFinset m p ↔ q ∈ leeSphere m p := by
  unfold leeSphereFinset leeSphere taxicabDist
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h
    change taxicabDist p q ≤ (m : ℤ) at h
    unfold taxicabDist at h
    have hx : |p.1 - q.1| ≤ (m : ℤ) := by linarith [abs_nonneg (p.2 - q.2)]
    have hy : |p.2 - q.2| ≤ (m : ℤ) := by linarith [abs_nonneg (p.1 - q.1)]
    rcases abs_le.mp hx with ⟨hx1, hx2⟩
    rcases abs_le.mp hy with ⟨hy1, hy2⟩
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, h⟩

/-- Chord sum over `j ∈ [-m, m]` equals `2*m^2 + 2*m + 1`. -/
theorem sum_chord_Icc (m : ℕ) :
    ∑ j ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), (2 * (m - j.natAbs) + 1) = 2 * m ^ 2 + 2 * m + 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : Finset.Icc (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) =
        insert (-((m + 1 : ℕ) : ℤ)) (insert ((m + 1 : ℕ) : ℤ) (Finset.Icc (-(m : ℤ)) (m : ℤ))) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot1 : (-((m + 1 : ℕ) : ℤ)) ∉ insert ((m + 1 : ℕ) : ℤ) (Finset.Icc (-(m : ℤ)) (m : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot2 : ((m + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    rw [h1, Finset.sum_insert hnot1, Finset.sum_insert hnot2]
    have hna1 : (-((m + 1 : ℕ) : ℤ)).natAbs = m + 1 := by omega
    have hna2 : (((m + 1 : ℕ) : ℤ)).natAbs = m + 1 := by omega
    rw [hna1, hna2, Nat.sub_self, Nat.mul_zero, Nat.zero_add]
    have hmid : ∑ j ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), (2 * ((m + 1) - j.natAbs) + 1) =
        ∑ j ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), ((2 * (m - j.natAbs) + 1) + 2) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Icc] at hj
      have hjle : j.natAbs ≤ m := by omega
      omega
    rw [hmid, Finset.sum_add_distrib, ih, Finset.sum_const, Int.card_Icc]
    have hcard : ((m : ℤ) + 1 - -(m : ℤ)).toNat = 2 * m + 1 := by omega
    rw [hcard]
    simp only [smul_eq_mul]
    ring

theorem card_leeSphereFinset (m : ℕ) (p : ℤ × ℤ) :
    (leeSphereFinset m p).card = 2 * m ^ 2 + 2 * m + 1 := by
  have hpart : leeSphereFinset m p =
      (Finset.Icc (p.1 - (m : ℤ)) (p.1 + (m : ℤ))).biUnion
        (fun x => (sphereColFinset m p x).image (fun y => (x, y))) := by
    ext ⟨x, y⟩
    simp only [mem_leeSphereFinset, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_Icc, mem_sphereColFinset]
    constructor
    · intro h
      change taxicabDist p (x, y) ≤ (m : ℤ) at h
      unfold taxicabDist at h
      have hx : |p.1 - x| ≤ (m : ℤ) := by linarith [abs_nonneg (p.2 - y)]
      rcases abs_le.mp hx with ⟨hx1, hx2⟩
      exact ⟨x, ⟨by omega, by omega⟩, y, h, rfl⟩
    · rintro ⟨x', _, y', hy', hxy⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
      exact hy'
  rw [hpart, Finset.card_biUnion]
  · have hsum : ∑ x ∈ Finset.Icc (p.1 - (m : ℤ)) (p.1 + (m : ℤ)),
        ((sphereColFinset m p x).image (fun y => (x, y))).card =
        ∑ j ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), (2 * (m - j.natAbs) + 1) := by
      refine Finset.sum_bij (fun x _ => x - p.1) ?_ ?_ ?_ ?_
      · intro x hx
        rw [Finset.mem_Icc] at hx ⊢
        omega
      · intro x₁ _ x₂ _ h
        omega
      · intro j hj
        rw [Finset.mem_Icc] at hj
        refine ⟨p.1 + j, ?_, by ring⟩
        rw [Finset.mem_Icc]
        omega
      · intro x hx
        rw [Finset.mem_Icc] at hx
        rw [Finset.card_image_of_injective _ (fun y₁ y₂ h => (Prod.mk.inj h).2)]
        rw [card_sphereColFinset]
        have hle : (x - p.1).natAbs ≤ m := by omega
        simp [hle]
    rw [hsum, sum_chord_Icc]
  · intro x₁ _ x₂ _ hne
    refine Finset.disjoint_left.mpr fun ⟨a, b⟩ ha hb => ?_
    simp only [Finset.mem_image] at ha hb
    obtain ⟨_, _, ha'⟩ := ha
    obtain ⟨_, _, hb'⟩ := hb
    have h1 : x₁ = a := (Prod.mk.inj ha').1
    have h2 : x₂ = a := (Prod.mk.inj hb').1
    exact hne (h1.trans h2.symm)

/-! ## Section 2: Odd Parameters, Plots, Validity, and Holes -/

/-- Sphere size `N = 2m^2 + 2m + 1` for odd `k = 2m - 1`. -/
def N_odd (m : ℕ) : ℕ := 2 * m ^ 2 + 2 * m + 1

/-- Minimal permutation size `n = 2m^2 + 2m` for odd `k = 2m - 1`. -/
def n_odd (m : ℕ) : ℕ := 2 * m ^ 2 + 2 * m

/-- Required minimum taxicab distance `d = k + 2 = 2m + 1` for odd `k = 2m - 1`. -/
def d_odd (m : ℕ) : ℕ := 2 * m + 1

theorem N_odd_pos (m : ℕ) : 0 < N_odd m := by
  unfold N_odd; omega

theorem n_odd_add_one (m : ℕ) : n_odd m + 1 = N_odd m := by
  unfold n_odd N_odd; omega

theorem n_odd_pos {m : ℕ} (hm : 1 ≤ m) : 0 < n_odd m := by
  unfold n_odd; have := hm; nlinarith

theorem d_odd_lt_N_odd {m : ℕ} (hm : 1 ≤ m) : d_odd m < N_odd m := by
  unfold d_odd N_odd; nlinarith

theorem d_odd_sq_eq (m : ℕ) : d_odd m ^ 2 + 1 = 2 * N_odd m := by
  unfold d_odd N_odd; ring

theorem two_mul_m_le_n_odd {m : ℕ} (hm : 1 ≤ m) : 2 * m ≤ n_odd m := by
  unfold n_odd; have := hm; nlinarith

/-- The 1-indexed plot point `(i + 1, w i + 1) ∈ [1, n]^2` of a permutation `w : Equiv.Perm (Fin n)`. -/
def plotPoint {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) : ℤ × ℤ :=
  ((i.val : ℤ) + 1, ((w i).val : ℤ) + 1)

theorem plotPoint_injective {n : ℕ} (w : Equiv.Perm (Fin n)) : Function.Injective (plotPoint w) := by
  intro i j h
  have hi : (i.val : ℤ) + 1 = (j.val : ℤ) + 1 := (Prod.mk.inj h).1
  exact Fin.ext (by omega)

theorem plotPoint_mem_box {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) :
    1 ≤ (plotPoint w i).1 ∧ (plotPoint w i).1 ≤ (n : ℤ) ∧
    1 ≤ (plotPoint w i).2 ∧ (plotPoint w i).2 ≤ (n : ℤ) := by
  unfold plotPoint
  have hi := i.isLt
  have hwi := (w i).isLt
  omega

/-- The plot of `w` as a set in `ℤ × ℤ`. -/
def plotSet {n : ℕ} (w : Equiv.Perm (Fin n)) : Set (ℤ × ℤ) :=
  Set.range (plotPoint w)

/-- The plot of `w` as a `Finset` in `ℤ × ℤ`. -/
def plotFinset {n : ℕ} (w : Equiv.Perm (Fin n)) : Finset (ℤ × ℤ) :=
  Finset.univ.image (plotPoint w)

/-- A permutation `w : Equiv.Perm (Fin n)` is valid at separation `d` iff distinct plot points
have taxicab distance at least `d` (equivalent to `breadth(w) ≥ d`, and by BHT Theorem 2.25
to being `(d - 2)`-prolific). -/
def IsValidPerm {n : ℕ} (d : ℕ) (w : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, i ≠ j → (d : ℤ) ≤ taxicabDist (plotPoint w i) (plotPoint w j)

instance instDecidablePredIsValidPerm (n d : ℕ) :
    DecidablePred (IsValidPerm (n := n) d) :=
  fun _w => Fintype.decidableForallFintype

/-- Validity for odd `k = 2m - 1` at minimal size `n_odd m` (`d_odd m = 2m + 1`). -/
def IsValidOdd (m : ℕ) (w : Equiv.Perm (Fin (n_odd m))) : Prop :=
  IsValidPerm (d_odd m) w

instance instDecidablePredIsValidOdd (m : ℕ) :
    DecidablePred (IsValidOdd m) :=
  instDecidablePredIsValidPerm (n_odd m) (d_odd m)

theorem isValidPerm_iff_plotSet {n d : ℕ} (w : Equiv.Perm (Fin n)) :
    IsValidPerm d w ↔
      ∀ p ∈ plotSet w, ∀ q ∈ plotSet w, p ≠ q → (d : ℤ) ≤ taxicabDist p q := by
  constructor
  · intro hw p hp q hq hpq
    obtain ⟨i, rfl⟩ := hp
    obtain ⟨j, rfl⟩ := hq
    apply hw
    intro hij; subst hij; exact hpq rfl
  · intro h i j hij
    apply h (plotPoint w i) ⟨i, rfl⟩ (plotPoint w j) ⟨j, rfl⟩
    intro heq
    exact hij (plotPoint_injective w heq)

/-- A lattice point `q` is covered by the radius-`m` Lee spheres around the plot of `w`. -/
def isCovered (m : ℕ) (w : Equiv.Perm (Fin (n_odd m))) (q : ℤ × ℤ) : Prop :=
  ∃ i : Fin (n_odd m), q ∈ leeSphere m (plotPoint w i)

/-- A cell `q ∈ [1, n]^2` is a hole of `w` if it is not covered by any sphere of `plot w`. -/
def isHole (m : ℕ) (w : Equiv.Perm (Fin (n_odd m))) (q : ℤ × ℤ) : Prop :=
  1 ≤ q.1 ∧ q.1 ≤ (n_odd m : ℤ) ∧ 1 ≤ q.2 ∧ q.2 ≤ (n_odd m : ℤ) ∧ ¬ isCovered m w q

/-- The finite set of all holes in `[1, n_odd m]^2`. -/
noncomputable def holesFinset (m : ℕ) (w : Equiv.Perm (Fin (n_odd m))) : Finset (ℤ × ℤ) :=
  letI := Classical.decPred (isCovered m w)
  ((Finset.Icc 1 (n_odd m : ℤ)) ×ˢ (Finset.Icc 1 (n_odd m : ℤ))).filter
    (fun q => ¬ isCovered m w q)

theorem mem_holesFinset {m : ℕ} {w : Equiv.Perm (Fin (n_odd m))} {q : ℤ × ℤ} :
    q ∈ holesFinset m w ↔ isHole m w q := by
  unfold holesFinset isHole
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

/-! ## Section 3: Explicit Odd Permutations `sigmaPlus` and `sigmaMinus` -/

private theorem d_mul_neg_d_mod (m : ℕ) (hm : 1 ≤ m) :
    (d_odd m * (N_odd m - d_odd m)) % N_odd m = 1 := by
  have hlt : d_odd m < N_odd m := d_odd_lt_N_odd hm
  have hd2 : 2 ≤ d_odd m := by unfold d_odd; omega
  have hN1 : 1 < N_odd m := by unfold N_odd; nlinarith
  have hid : d_odd m * (N_odd m - d_odd m) = (d_odd m - 2) * N_odd m + 1 := by
    have hsq := d_odd_sq_eq m
    zify [hlt.le, hd2]
    linarith
  rw [hid, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hN1]

private theorem mul_d_range {m x : ℕ} (hm : 1 ≤ m) (hx1 : 1 ≤ x) (hxn : x ≤ n_odd m) :
    1 ≤ (x * d_odd m) % N_odd m ∧ (x * d_odd m) % N_odd m ≤ n_odd m := by
  have hN : 0 < N_odd m := N_odd_pos m
  have hN1 : N_odd m = n_odd m + 1 := (n_odd_add_one m).symm
  have hxlt : x < N_odd m := by omega
  have hlt : (x * d_odd m) % N_odd m < N_odd m := Nat.mod_lt _ hN
  have hne : (x * d_odd m) % N_odd m ≠ 0 := by
    intro h0
    have hinv := d_mul_neg_d_mod m hm
    have h1 : (((x * d_odd m) % N_odd m) * (N_odd m - d_odd m)) % N_odd m = 0 := by
      rw [h0, Nat.zero_mul, Nat.zero_mod]
    rw [Nat.mod_mul_mod, mul_assoc, Nat.mul_mod x, hinv, Nat.mul_one,
      Nat.mod_mod, Nat.mod_eq_of_lt hxlt] at h1
    omega
  omega

private theorem mul_neg_d_range {m x : ℕ} (hm : 1 ≤ m) (hx1 : 1 ≤ x) (hxn : x ≤ n_odd m) :
    1 ≤ (x * (N_odd m - d_odd m)) % N_odd m ∧
    (x * (N_odd m - d_odd m)) % N_odd m ≤ n_odd m := by
  have hN : 0 < N_odd m := N_odd_pos m
  have hN1 : N_odd m = n_odd m + 1 := (n_odd_add_one m).symm
  have hxlt : x < N_odd m := by omega
  have hlt : (x * (N_odd m - d_odd m)) % N_odd m < N_odd m := Nat.mod_lt _ hN
  have hne : (x * (N_odd m - d_odd m)) % N_odd m ≠ 0 := by
    intro h0
    have hinv := d_mul_neg_d_mod m hm
    have h1 : (((x * (N_odd m - d_odd m)) % N_odd m) * d_odd m) % N_odd m = 0 := by
      rw [h0, Nat.zero_mul, Nat.zero_mod]
    rw [Nat.mod_mul_mod, mul_assoc, mul_comm (N_odd m - d_odd m) (d_odd m),
      Nat.mul_mod x, hinv, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hxlt] at h1
    omega
  omega

private theorem mul_d_left_inv {m x : ℕ} (hm : 1 ≤ m) (hx : x < N_odd m) :
    ((((x * d_odd m) % N_odd m) * (N_odd m - d_odd m)) % N_odd m) = x := by
  rw [Nat.mod_mul_mod, mul_assoc, Nat.mul_mod x, d_mul_neg_d_mod m hm,
    Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hx]

private theorem mul_d_right_inv {m y : ℕ} (hm : 1 ≤ m) (hy : y < N_odd m) :
    ((((y * (N_odd m - d_odd m)) % N_odd m) * d_odd m) % N_odd m) = y := by
  rw [Nat.mod_mul_mod, mul_assoc, mul_comm (N_odd m - d_odd m) (d_odd m),
    Nat.mul_mod y, d_mul_neg_d_mod m hm, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hy]

/-- The minimal odd `k`-prolific permutation `σ_k(i) = d * i mod N` (`1`-indexed). -/
def sigmaPlus (m : ℕ) : Equiv.Perm (Fin (n_odd m)) :=
  if hm : 1 ≤ m then
    { toFun := fun i =>
        ⟨((i.val + 1) * d_odd m) % N_odd m - 1, by
          have hr := mul_d_range hm (by omega) (by omega : i.val + 1 ≤ n_odd m)
          omega⟩
      invFun := fun j =>
        ⟨((j.val + 1) * (N_odd m - d_odd m)) % N_odd m - 1, by
          have hr := mul_neg_d_range hm (by omega) (by omega : j.val + 1 ≤ n_odd m)
          omega⟩
      left_inv := fun i => by
        ext
        have hN1 : N_odd m = n_odd m + 1 := (n_odd_add_one m).symm
        have hr := mul_d_range hm (by omega) (by omega : i.val + 1 ≤ n_odd m)
        change (((((i.val + 1) * d_odd m) % N_odd m - 1) + 1) * (N_odd m - d_odd m)) % N_odd m - 1 = i.val
        rw [Nat.sub_add_cancel hr.1, mul_d_left_inv hm (by omega)]
        omega
      right_inv := fun j => by
        ext
        have hN1 : N_odd m = n_odd m + 1 := (n_odd_add_one m).symm
        have hr := mul_neg_d_range hm (by omega) (by omega : j.val + 1 ≤ n_odd m)
        change (((((j.val + 1) * (N_odd m - d_odd m)) % N_odd m - 1) + 1) * d_odd m) % N_odd m - 1 = j.val
        rw [Nat.sub_add_cancel hr.1, mul_d_right_inv hm (by omega)]
        omega }
  else
    Equiv.refl _

/-- The reverse/complement of `sigmaPlus m`: `σ⁻(i) = -d * i mod N` (`1`-indexed). -/
def sigmaMinus (m : ℕ) : Equiv.Perm (Fin (n_odd m)) :=
  (sigmaPlus m).symm

theorem sigmaPlus_val {m : ℕ} (hm : 1 ≤ m) (i : Fin (n_odd m)) :
    ((sigmaPlus m i).val + 1) = ((i.val + 1) * d_odd m) % N_odd m := by
  unfold sigmaPlus
  split_ifs
  have hr := mul_d_range hm (by omega) (by omega : i.val + 1 ≤ n_odd m)
  exact Nat.sub_add_cancel hr.1

theorem sigmaMinus_val {m : ℕ} (hm : 1 ≤ m) (i : Fin (n_odd m)) :
    ((sigmaMinus m i).val + 1) = ((i.val + 1) * (N_odd m - d_odd m)) % N_odd m := by
  unfold sigmaMinus sigmaPlus
  split_ifs
  have hr := mul_neg_d_range hm (by omega) (by omega : i.val + 1 ≤ n_odd m)
  exact Nat.sub_add_cancel hr.1

theorem sigmaPlus_mod_eq {m : ℕ} (hm : 1 ≤ m) (i : Fin (n_odd m)) :
    ((sigmaPlus m i).val : ℤ) + 1 ≡ (d_odd m : ℤ) * ((i.val : ℤ) + 1) [ZMOD (N_odd m : ℤ)] := by
  have h := sigmaPlus_val hm i
  have h1 : (((sigmaPlus m i).val + 1 : ℕ) : ℤ) =
      ((((i.val + 1) * d_odd m) % N_odd m : ℕ) : ℤ) := by exact_mod_cast h
  rw [Nat.cast_add, Nat.cast_one] at h1
  rw [h1, Int.natCast_mod, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp [Int.ModEq, mul_comm]

theorem sigmaMinus_mod_eq {m : ℕ} (hm : 1 ≤ m) (i : Fin (n_odd m)) :
    ((sigmaMinus m i).val : ℤ) + 1 ≡ -((d_odd m : ℤ) * ((i.val : ℤ) + 1)) [ZMOD (N_odd m : ℤ)] := by
  have h := sigmaMinus_val hm i
  have hlt : d_odd m < N_odd m := d_odd_lt_N_odd hm
  have h1 : (((sigmaMinus m i).val + 1 : ℕ) : ℤ) =
      ((((i.val + 1) * (N_odd m - d_odd m)) % N_odd m : ℕ) : ℤ) := by exact_mod_cast h
  rw [Nat.cast_add, Nat.cast_one] at h1
  rw [h1, Int.natCast_mod, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hlt.le]
  rw [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero]
  have hdvd : (N_odd m : ℤ) ∣
      (((i.val : ℤ) + 1) * ((N_odd m : ℤ) - (d_odd m : ℤ))) % (N_odd m : ℤ) -
        -((d_odd m : ℤ) * ((i.val : ℤ) + 1)) := by
    have heq : (((i.val : ℤ) + 1) * ((N_odd m : ℤ) - (d_odd m : ℤ))) =
        ((i.val : ℤ) + 1) * (N_odd m : ℤ) - (d_odd m : ℤ) * ((i.val : ℤ) + 1) := by ring
    rw [heq]
    have hmod : (((i.val : ℤ) + 1) * (N_odd m : ℤ) - (d_odd m : ℤ) * ((i.val : ℤ) + 1)) % (N_odd m : ℤ) ≡
        -((d_odd m : ℤ) * ((i.val : ℤ) + 1)) [ZMOD (N_odd m : ℤ)] := by
      rw [Int.ModEq, Int.emod_emod]
      simp [sub_eq_add_neg, Int.add_emod]
    exact Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod)
  exact Int.emod_eq_zero_of_dvd hdvd

/-! ## Section 4: Symmetries of the Square (`D₄`) -/

/-- Reverse of a permutation on `Fin n`: `(x, y) ↦ (n + 1 - x, y)`. -/
def permReverse {n : ℕ} (w : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans w

/-- Complement of a permutation on `Fin n`: `(x, y) ↦ (x, n + 1 - y)`. -/
def permComplement {n : ℕ} (w : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  w.trans Fin.revPerm

/-- Inverse of a permutation on `Fin n`: `(x, y) ↦ (y, x)` (transpose). -/
def permInverse {n : ℕ} (w : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  w.symm

/-- 90-degree rotation of a permutation on `Fin n`: `(x, y) ↦ (n + 1 - y, x)`. -/
def permRot90 {n : ℕ} (w : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans w.symm

theorem permReverse_rev {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) :
    permReverse w i = w (Fin.rev i) := rfl

theorem permComplement_val {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) :
    permComplement w i = Fin.rev (w i) := rfl

theorem permInverse_val {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) :
    permInverse w i = w.symm i := rfl

theorem permRot90_val {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) :
    permRot90 w i = w.symm (Fin.rev i) := rfl

theorem fin_rev_add_one {n : ℕ} (i : Fin n) :
    ((Fin.rev i).val : ℤ) + 1 = ((n : ℤ) + 1) - ((i.val : ℤ) + 1) := by
  rw [Fin.val_rev]
  have hi := i.isLt
  omega

/-- Pointwise reflections and transposition on `ℤ × ℤ` for the `[1, n]^2` box (`N = n + 1`). -/
def ptFlipX (N : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := (N - p.1, p.2)
def ptFlipY (N : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := (p.1, N - p.2)
def ptTranspose (p : ℤ × ℤ) : ℤ × ℤ := (p.2, p.1)
def ptRot90 (N : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := (N - p.2, p.1)

theorem taxicabDist_ptFlipX (N : ℤ) (p q : ℤ × ℤ) :
    taxicabDist (ptFlipX N p) (ptFlipX N q) = taxicabDist p q := by
  unfold ptFlipX taxicabDist; simp only [sub_sub_sub_cancel_left, abs_sub_comm p.1 q.1]

theorem taxicabDist_ptFlipX_left (N : ℤ) (p q : ℤ × ℤ) :
    taxicabDist (ptFlipX N p) q = taxicabDist p (ptFlipX N q) := by
  rw [← taxicabDist_ptFlipX N (ptFlipX N p) q]
  simp [ptFlipX]

theorem taxicabDist_ptFlipY (N : ℤ) (p q : ℤ × ℤ) :
    taxicabDist (ptFlipY N p) (ptFlipY N q) = taxicabDist p q := by
  unfold ptFlipY taxicabDist; simp only [sub_sub_sub_cancel_left, abs_sub_comm p.2 q.2]

theorem taxicabDist_ptFlipY_left (N : ℤ) (p q : ℤ × ℤ) :
    taxicabDist (ptFlipY N p) q = taxicabDist p (ptFlipY N q) := by
  rw [← taxicabDist_ptFlipY N (ptFlipY N p) q]
  simp [ptFlipY]

theorem taxicabDist_ptTranspose (p q : ℤ × ℤ) :
    taxicabDist (ptTranspose p) (ptTranspose q) = taxicabDist p q := by
  unfold ptTranspose taxicabDist
  dsimp only
  rw [add_comm]

theorem taxicabDist_ptTranspose_left (p q : ℤ × ℤ) :
    taxicabDist (ptTranspose p) q = taxicabDist p (ptTranspose q) := by
  rw [← taxicabDist_ptTranspose (ptTranspose p) q]
  simp [ptTranspose]

theorem taxicabDist_ptRot90 (N : ℤ) (p q : ℤ × ℤ) :
    taxicabDist (ptRot90 N p) (ptRot90 N q) = taxicabDist p q := by
  unfold ptRot90 taxicabDist
  dsimp only
  simp only [sub_sub_sub_cancel_left, abs_sub_comm p.2 q.2]
  rw [add_comm]

theorem plotPoint_permReverse {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) :
    plotPoint (permReverse w) (Fin.rev i) = ptFlipX ((n : ℤ) + 1) (plotPoint w i) := by
  unfold plotPoint ptFlipX
  rw [permReverse_rev, Fin.rev_rev, fin_rev_add_one]

theorem plotPoint_permComplement {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) :
    plotPoint (permComplement w) i = ptFlipY ((n : ℤ) + 1) (plotPoint w i) := by
  unfold plotPoint ptFlipY
  rw [permComplement_val, fin_rev_add_one]

theorem plotPoint_permInverse {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) :
    plotPoint (permInverse w) (w i) = ptTranspose (plotPoint w i) := by
  unfold plotPoint ptTranspose
  rw [permInverse_val, Equiv.symm_apply_apply]

theorem plotPoint_permRot90 {n : ℕ} (w : Equiv.Perm (Fin n)) (i : Fin n) :
    plotPoint (permRot90 w) (Fin.rev (w i)) = ptRot90 ((n : ℤ) + 1) (plotPoint w i) := by
  unfold plotPoint ptRot90
  rw [permRot90_val, Fin.rev_rev, Equiv.symm_apply_apply, fin_rev_add_one]

theorem isValidPerm_permReverse {n d : ℕ} {w : Equiv.Perm (Fin n)} (hw : IsValidPerm d w) :
    IsValidPerm d (permReverse w) := by
  intro i j hij
  have h := hw (Fin.rev i) (Fin.rev j) (fun h => hij (Fin.rev_inj.mp h))
  have hi : plotPoint (permReverse w) i = ptFlipX ((n : ℤ) + 1) (plotPoint w (Fin.rev i)) := by
    simpa [Fin.rev_rev] using plotPoint_permReverse w (Fin.rev i)
  have hj : plotPoint (permReverse w) j = ptFlipX ((n : ℤ) + 1) (plotPoint w (Fin.rev j)) := by
    simpa [Fin.rev_rev] using plotPoint_permReverse w (Fin.rev j)
  rw [hi, hj, taxicabDist_ptFlipX]
  exact h

theorem isValidPerm_permComplement {n d : ℕ} {w : Equiv.Perm (Fin n)} (hw : IsValidPerm d w) :
    IsValidPerm d (permComplement w) := by
  intro i j hij
  have h := hw i j hij
  rw [plotPoint_permComplement, plotPoint_permComplement, taxicabDist_ptFlipY]
  exact h

theorem isValidPerm_permInverse {n d : ℕ} {w : Equiv.Perm (Fin n)} (hw : IsValidPerm d w) :
    IsValidPerm d (permInverse w) := by
  intro i j hij
  have h := hw (w.symm i) (w.symm j) (w.symm.injective.ne hij)
  have hi : plotPoint (permInverse w) i = ptTranspose (plotPoint w (w.symm i)) := by
    simpa using plotPoint_permInverse w (w.symm i)
  have hj : plotPoint (permInverse w) j = ptTranspose (plotPoint w (w.symm j)) := by
    simpa using plotPoint_permInverse w (w.symm j)
  rw [hi, hj, taxicabDist_ptTranspose]
  exact h

theorem isValidPerm_permRot90 {n d : ℕ} {w : Equiv.Perm (Fin n)} (hw : IsValidPerm d w) :
    IsValidPerm d (permRot90 w) := by
  unfold permRot90
  exact isValidPerm_permReverse (isValidPerm_permInverse hw)

theorem isCovered_permReverse {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) (q : ℤ × ℤ) :
    isCovered m (permReverse w) q ↔ isCovered m w (ptFlipX (N_odd m : ℤ) q) := by
  have hN : ((n_odd m : ℤ) + 1) = (N_odd m : ℤ) := by exact_mod_cast n_odd_add_one m
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨Fin.rev i, ?_⟩
    change taxicabDist (plotPoint w (Fin.rev i)) (ptFlipX (N_odd m : ℤ) q) ≤ (m : ℤ)
    change taxicabDist (plotPoint (permReverse w) i) q ≤ (m : ℤ) at hi
    have hpi : plotPoint (permReverse w) i = ptFlipX (N_odd m : ℤ) (plotPoint w (Fin.rev i)) := by
      rw [← hN]; simpa [Fin.rev_rev] using plotPoint_permReverse w (Fin.rev i)
    rwa [hpi, taxicabDist_ptFlipX_left] at hi
  · rintro ⟨i, hi⟩
    refine ⟨Fin.rev i, ?_⟩
    change taxicabDist (plotPoint (permReverse w) (Fin.rev i)) q ≤ (m : ℤ)
    change taxicabDist (plotPoint w i) (ptFlipX (N_odd m : ℤ) q) ≤ (m : ℤ) at hi
    have hpi : plotPoint (permReverse w) (Fin.rev i) = ptFlipX (N_odd m : ℤ) (plotPoint w i) := by
      rw [← hN]; exact plotPoint_permReverse w i
    rwa [hpi, taxicabDist_ptFlipX_left]

theorem isCovered_permComplement {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) (q : ℤ × ℤ) :
    isCovered m (permComplement w) q ↔ isCovered m w (ptFlipY (N_odd m : ℤ) q) := by
  have hN : ((n_odd m : ℤ) + 1) = (N_odd m : ℤ) := by exact_mod_cast n_odd_add_one m
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change taxicabDist (plotPoint w i) (ptFlipY (N_odd m : ℤ) q) ≤ (m : ℤ)
    change taxicabDist (plotPoint (permComplement w) i) q ≤ (m : ℤ) at hi
    have hpi : plotPoint (permComplement w) i = ptFlipY (N_odd m : ℤ) (plotPoint w i) := by
      rw [← hN]; exact plotPoint_permComplement w i
    rwa [hpi, taxicabDist_ptFlipY_left] at hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change taxicabDist (plotPoint (permComplement w) i) q ≤ (m : ℤ)
    change taxicabDist (plotPoint w i) (ptFlipY (N_odd m : ℤ) q) ≤ (m : ℤ) at hi
    have hpi : plotPoint (permComplement w) i = ptFlipY (N_odd m : ℤ) (plotPoint w i) := by
      rw [← hN]; exact plotPoint_permComplement w i
    rwa [hpi, taxicabDist_ptFlipY_left]

theorem isCovered_permInverse {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) (q : ℤ × ℤ) :
    isCovered m (permInverse w) q ↔ isCovered m w (ptTranspose q) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨w.symm i, ?_⟩
    change taxicabDist (plotPoint w (w.symm i)) (ptTranspose q) ≤ (m : ℤ)
    change taxicabDist (plotPoint (permInverse w) i) q ≤ (m : ℤ) at hi
    have hpi : plotPoint (permInverse w) i = ptTranspose (plotPoint w (w.symm i)) := by
      simpa using plotPoint_permInverse w (w.symm i)
    rwa [hpi, taxicabDist_ptTranspose_left] at hi
  · rintro ⟨i, hi⟩
    refine ⟨w i, ?_⟩
    change taxicabDist (plotPoint (permInverse w) (w i)) q ≤ (m : ℤ)
    change taxicabDist (plotPoint w i) (ptTranspose q) ≤ (m : ℤ) at hi
    have hpi : plotPoint (permInverse w) (w i) = ptTranspose (plotPoint w i) :=
      plotPoint_permInverse w i
    rwa [hpi, taxicabDist_ptTranspose_left]

theorem isHole_permReverse {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) (q : ℤ × ℤ) :
    isHole m (permReverse w) q ↔ isHole m w (ptFlipX (N_odd m : ℤ) q) := by
  unfold isHole ptFlipX
  rw [isCovered_permReverse]
  have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  dsimp only
  constructor <;> rintro ⟨h1, h2, h3, h4, hc⟩ <;> exact ⟨by omega, by omega, h3, h4, hc⟩

theorem isHole_permComplement {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) (q : ℤ × ℤ) :
    isHole m (permComplement w) q ↔ isHole m w (ptFlipY (N_odd m : ℤ) q) := by
  unfold isHole ptFlipY
  rw [isCovered_permComplement]
  have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  dsimp only
  constructor <;> rintro ⟨h1, h2, h3, h4, hc⟩ <;> exact ⟨h1, h2, by omega, by omega, hc⟩

theorem isHole_permInverse {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) (q : ℤ × ℤ) :
    isHole m (permInverse w) q ↔ isHole m w (ptTranspose q) := by
  unfold isHole ptTranspose
  rw [isCovered_permInverse]
  dsimp only
  tauto

/-- The eight symmetries of the square (`D₄`): four rotations `r0..r3` and four reflections `s0..s3`. -/
inductive SquareSym : Type
  | r0 | r1 | r2 | r3
  | s0 | s1 | s2 | s3
  deriving DecidableEq

/-- Action of `SquareSym` on `Equiv.Perm (Fin n)`. -/
def applySymPerm {n : ℕ} : SquareSym → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)
  | .r0, w => w
  | .r1, w => permRot90 w
  | .r2, w => permReverse (permComplement w)
  | .r3, w => permComplement (permInverse w)
  | .s0, w => permReverse w
  | .s1, w => permInverse w
  | .s2, w => permComplement w
  | .s3, w => permReverse (permComplement (permInverse w))

/-- Action of `SquareSym` on `ℤ × ℤ` (with `N = n + 1`). -/
def applySymPt (N : ℤ) : SquareSym → ℤ × ℤ → ℤ × ℤ
  | .r0, p => p
  | .r1, p => ptRot90 N p
  | .r2, p => ptFlipX N (ptFlipY N p)
  | .r3, p => ptFlipY N (ptTranspose p)
  | .s0, p => ptFlipX N p
  | .s1, p => ptTranspose p
  | .s2, p => ptFlipY N p
  | .s3, p => ptFlipX N (ptFlipY N (ptTranspose p))

theorem isValidPerm_applySymPerm {n d : ℕ} (g : SquareSym) {w : Equiv.Perm (Fin n)}
    (hw : IsValidPerm d w) : IsValidPerm d (applySymPerm g w) := by
  cases g
  · exact hw
  · exact isValidPerm_permRot90 hw
  · exact isValidPerm_permReverse (isValidPerm_permComplement hw)
  · exact isValidPerm_permComplement (isValidPerm_permInverse hw)
  · exact isValidPerm_permReverse hw
  · exact isValidPerm_permInverse hw
  · exact isValidPerm_permComplement hw
  · exact isValidPerm_permReverse (isValidPerm_permComplement (isValidPerm_permInverse hw))

theorem taxicabDist_applySymPt (N : ℤ) (g : SquareSym) (p q : ℤ × ℤ) :
    taxicabDist (applySymPt N g p) (applySymPt N g q) = taxicabDist p q := by
  cases g
  · rfl
  · exact taxicabDist_ptRot90 N p q
  · simp [applySymPt, taxicabDist_ptFlipX, taxicabDist_ptFlipY]
  · simp [applySymPt, taxicabDist_ptFlipY, taxicabDist_ptTranspose]
  · exact taxicabDist_ptFlipX N p q
  · exact taxicabDist_ptTranspose p q
  · exact taxicabDist_ptFlipY N p q
  · simp [applySymPt, taxicabDist_ptFlipX, taxicabDist_ptFlipY, taxicabDist_ptTranspose]

end MinimalProlific
