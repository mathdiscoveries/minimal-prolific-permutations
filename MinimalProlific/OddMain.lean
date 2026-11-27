/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MinimalProlific.LeeLattice

import Mathlib.Tactic

/-!
# Headline Theorems for Odd `k`-Prolific Permutations (`MinimalProlific.OddMain`)

Exports the paper-exact classification and symmetry theorems for Theorem A
(Bevan–Homberger–Tenner JCTA 2018 Conjecture 5.1 for every odd `k = 2m - 1`, `m ≥ 1`):
- `odd_minimal_prolific_classification`: `IsValidOdd m w ↔ w = sigmaPlus m ∨ w = sigmaMinus m`.
- `odd_minimal_prolific_card_eq_two`: `Fintype.card { w // IsValidOdd m w } = 2`.
- `odd_symmetries_single_orbit`: `sigmaPlus m ≠ sigmaMinus m`, the two solutions are mutually
  reverse/complement/inverse/anti-transpose, fixed by all rotations (`D₄` subgroup), and form a
  single symmetry orbit under `D₄`.
- `lee_tiling_classification`: every radius-`m` Lee tiling of `ℤ^2` containing `(0, 0)` equals
  `LambdaPlus m` or `LambdaMinus m`.
-/

@[expose] public section

namespace MinimalProlific

/-! ## Section 1: Distinctness and `D₄` Action on `sigmaPlus` and `sigmaMinus` -/

theorem sigmaPlus_ne_sigmaMinus {m : ℕ} (hm : 1 ≤ m) : sigmaPlus m ≠ sigmaMinus m := by
  intro heq
  let z0 : Fin (n_odd m) := ⟨0, n_odd_pos hm⟩
  have h0 := congrArg (fun w : Equiv.Perm (Fin (n_odd m)) => (w z0).val + 1) heq
  rw [sigmaPlus_val hm z0, sigmaMinus_val hm z0] at h0
  have h1 : (z0.val + 1) * d_odd m = d_odd m := by simp [z0]
  have h2 : (z0.val + 1) * (N_odd m - d_odd m) = N_odd m - d_odd m := by simp [z0]
  rw [h1, h2] at h0
  have hlt1 : d_odd m < N_odd m := d_odd_lt_N_odd hm
  have hlt2 : N_odd m - d_odd m < N_odd m := Nat.sub_lt (N_odd_pos m) (by unfold d_odd; omega)
  rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at h0
  unfold d_odd N_odd at h0
  omega

private theorem perm_eq_of_add_one_modEq {m : ℕ} (u v : Equiv.Perm (Fin (n_odd m)))
    (h : ∀ i : Fin (n_odd m),
      ((u i).val : ℤ) + 1 ≡ ((v i).val : ℤ) + 1 [ZMOD (N_odd m : ℤ)]) :
    u = v := by
  ext i
  have hN1 : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  have hb1 : 0 ≤ ((u i).val : ℤ) + 1 ∧ ((u i).val : ℤ) + 1 < (N_odd m : ℤ) := by
    have := (u i).isLt; omega
  have hb2 : 0 ≤ ((v i).val : ℤ) + 1 ∧ ((v i).val : ℤ) + 1 < (N_odd m : ℤ) := by
    have := (v i).isLt; omega
  have hi := h i
  rw [Int.ModEq, Int.emod_eq_of_lt hb1.1 hb1.2, Int.emod_eq_of_lt hb2.1 hb2.2] at hi
  omega

theorem permReverse_sigmaPlus {m : ℕ} (hm : 1 ≤ m) :
    permReverse (sigmaPlus m) = sigmaMinus m := by
  apply perm_eq_of_add_one_modEq
  intro i
  rw [permReverse_rev]
  have h1 := sigmaPlus_mod_eq hm (Fin.rev i)
  have h2 := sigmaMinus_mod_eq hm i
  have hN1 : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  have hrev : ((Fin.rev i).val : ℤ) + 1 = (N_odd m : ℤ) - ((i.val : ℤ) + 1) := by
    rw [fin_rev_add_one, hN1]
  rw [hrev] at h1
  have hmod : (d_odd m : ℤ) * ((N_odd m : ℤ) - ((i.val : ℤ) + 1)) ≡
      -((d_odd m : ℤ) * ((i.val : ℤ) + 1)) [ZMOD (N_odd m : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d_odd m : ℤ), ?_⟩
    ring
  exact h1.trans (hmod.trans h2.symm)

theorem permComplement_sigmaPlus {m : ℕ} (hm : 1 ≤ m) :
    permComplement (sigmaPlus m) = sigmaMinus m := by
  apply perm_eq_of_add_one_modEq
  intro i
  rw [permComplement_val]
  have h1 := sigmaPlus_mod_eq hm i
  have h2 := sigmaMinus_mod_eq hm i
  have hN1 : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  have hrev : ((Fin.rev (sigmaPlus m i)).val : ℤ) + 1 =
      (N_odd m : ℤ) - (((sigmaPlus m i).val : ℤ) + 1) := by
    rw [fin_rev_add_one, hN1]
  rw [hrev]
  have hneg : (N_odd m : ℤ) - (((sigmaPlus m i).val : ℤ) + 1) ≡
      -((d_odd m : ℤ) * ((i.val : ℤ) + 1)) [ZMOD (N_odd m : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    obtain ⟨k, hk⟩ := h1.dvd
    refine ⟨-k - 1, ?_⟩
    linarith
  exact hneg.trans h2.symm

theorem permInverse_sigmaPlus (m : ℕ) :
    permInverse (sigmaPlus m) = sigmaMinus m := rfl

theorem permReverse_permReverse {n : ℕ} (w : Equiv.Perm (Fin n)) :
    permReverse (permReverse w) = w := by
  ext i
  simp [permReverse_rev, Fin.rev_rev]

theorem permComplement_permComplement {n : ℕ} (w : Equiv.Perm (Fin n)) :
    permComplement (permComplement w) = w := by
  ext i
  simp [permComplement_val, Fin.rev_rev]

theorem permInverse_permInverse {n : ℕ} (w : Equiv.Perm (Fin n)) :
    permInverse (permInverse w) = w :=
  Equiv.symm_symm w

theorem permReverse_sigmaMinus {m : ℕ} (hm : 1 ≤ m) :
    permReverse (sigmaMinus m) = sigmaPlus m := by
  rw [← permReverse_sigmaPlus hm, permReverse_permReverse]

theorem permComplement_sigmaMinus {m : ℕ} (hm : 1 ≤ m) :
    permComplement (sigmaMinus m) = sigmaPlus m := by
  rw [← permComplement_sigmaPlus hm, permComplement_permComplement]

theorem permInverse_sigmaMinus (m : ℕ) :
    permInverse (sigmaMinus m) = sigmaPlus m := by
  rw [← permInverse_sigmaPlus m, permInverse_permInverse]

theorem permRot90_sigmaPlus {m : ℕ} (hm : 1 ≤ m) :
    permRot90 (sigmaPlus m) = sigmaPlus m := by
  change permReverse (permInverse (sigmaPlus m)) = sigmaPlus m
  rw [permInverse_sigmaPlus, permReverse_sigmaMinus hm]

theorem permRot90_sigmaMinus {m : ℕ} (hm : 1 ≤ m) :
    permRot90 (sigmaMinus m) = sigmaMinus m := by
  change permReverse (permInverse (sigmaMinus m)) = sigmaMinus m
  rw [permInverse_sigmaMinus, permReverse_sigmaPlus hm]

/-! ## Section 2: Headline Theorems for Odd Minimal `k`-Prolific Permutations -/

/-- **Theorem A (Exact Classification for Every Odd `k = 2m - 1`, `m ≥ 1`):**
A permutation `w : Equiv.Perm (Fin (n_odd m))` is valid (`IsValidOdd m w`, i.e. breadth `≥ 2m + 1`)
if and only if `w = sigmaPlus m` or `w = sigmaMinus m`. -/
theorem odd_minimal_prolific_classification (m : ℕ) (hm : 1 ≤ m)
    (w : Equiv.Perm (Fin (n_odd m))) :
    IsValidOdd m w ↔ w = sigmaPlus m ∨ w = sigmaMinus m := by
  constructor
  · exact validOdd_eq_sigmaPlus_or_sigmaMinus hm
  · rintro (rfl | rfl)
    · exact sigmaPlus_isValidOdd hm
    · exact sigmaMinus_isValidOdd hm

/-- **Theorem A (Exact Enumeration):** For every `m ≥ 1` (`k = 2m - 1`), there are exactly
`2` valid minimal `k`-prolific permutations of length `n_odd m = 2m^2 + 2m`. -/
theorem odd_minimal_prolific_card_eq_two (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card { w : Equiv.Perm (Fin (n_odd m)) // IsValidOdd m w } = 2 := by
  let f : Bool → { w : Equiv.Perm (Fin (n_odd m)) // IsValidOdd m w } :=
    fun b => if b then ⟨sigmaMinus m, sigmaMinus_isValidOdd hm⟩
             else ⟨sigmaPlus m, sigmaPlus_isValidOdd hm⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro b₁ b₂ h
      have hv := congrArg Subtype.val h
      cases b₁ <;> cases b₂
      · rfl
      · exfalso; exact sigmaPlus_ne_sigmaMinus hm (by simpa [f] using hv)
      · exfalso; exact sigmaPlus_ne_sigmaMinus hm (by simpa [f] using hv.symm)
      · rfl
    · rintro ⟨w, hw⟩
      rcases (odd_minimal_prolific_classification m hm w).mp hw with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
  rw [← Fintype.card_congr (Equiv.ofBijective f hbij), Fintype.card_bool]

/-- **Theorem A (`D₄` Symmetry Orbit):** For every `m ≥ 1`, `sigmaPlus m` and `sigmaMinus m` are
distinct, mutually related by reverse, complement, and inverse, invariant under 90-degree rotation,
and form a single `SquareSym` (`D₄`) orbit of size 2. -/
theorem odd_symmetries_single_orbit (m : ℕ) (hm : 1 ≤ m) :
    sigmaPlus m ≠ sigmaMinus m ∧
    permReverse (sigmaPlus m) = sigmaMinus m ∧
    permComplement (sigmaPlus m) = sigmaMinus m ∧
    permInverse (sigmaPlus m) = sigmaMinus m ∧
    permRot90 (sigmaPlus m) = sigmaPlus m ∧
    permRot90 (sigmaMinus m) = sigmaMinus m ∧
    (∀ g : SquareSym,
      (applySymPerm g (sigmaPlus m) = sigmaPlus m ∨
       applySymPerm g (sigmaPlus m) = sigmaMinus m) ∧
      (applySymPerm g (sigmaMinus m) = sigmaPlus m ∨
       applySymPerm g (sigmaMinus m) = sigmaMinus m)) ∧
    (∃ g : SquareSym, applySymPerm g (sigmaPlus m) = sigmaMinus m) := by
  refine ⟨sigmaPlus_ne_sigmaMinus hm, permReverse_sigmaPlus hm, permComplement_sigmaPlus hm,
    permInverse_sigmaPlus m, permRot90_sigmaPlus hm, permRot90_sigmaMinus hm, ?_,
    ⟨SquareSym.s0, permReverse_sigmaPlus hm⟩⟩
  intro g
  have hc_plus : permComplement (sigmaPlus m) = sigmaMinus m := permComplement_sigmaPlus hm
  have hc_minus : permComplement (sigmaMinus m) = sigmaPlus m := permComplement_sigmaMinus hm
  have hr_plus : permReverse (sigmaPlus m) = sigmaMinus m := permReverse_sigmaPlus hm
  have hr_minus : permReverse (sigmaMinus m) = sigmaPlus m := permReverse_sigmaMinus hm
  have hi_plus : permInverse (sigmaPlus m) = sigmaMinus m := permInverse_sigmaPlus m
  have hi_minus : permInverse (sigmaMinus m) = sigmaPlus m := permInverse_sigmaMinus m
  cases g <;> simp only [applySymPerm, hr_plus, hr_minus, hc_plus, hc_minus, hi_plus, hi_minus,
    permRot90_sigmaPlus hm, permRot90_sigmaMinus hm] <;> tauto

/-- **Theorem A (Lee Lattice Tiling Classification):** Every radius-`m` Lee tiling `T ⊆ ℤ × ℤ`
containing `(0, 0)` equals `LambdaPlus m` or `LambdaMinus m`. -/
theorem lee_tiling_classification (m : ℕ) (hm : 1 ≤ m) (T : Set (ℤ × ℤ))
    (hT : IsLeeTiling m T) (hO : (0, 0) ∈ T) :
    T = LambdaPlus m ∨ T = LambdaMinus m :=
  claim7_lee_tiling_classification m hm T hT hO

/-- **Theorem 1 (Bundled Paper-Exact Main Theorem for Every Odd `k = 2m - 1`, `m ≥ 1`):**
Combines the iff classification (`IsValidOdd m w ↔ w = sigmaPlus m ∨ w = sigmaMinus m`),
exact count `2`, distinctness, mutual reverse/complement/inverse, 90-degree rotation invariance,
and single `D₄` orbit of size `2`. -/
theorem theorem_odd_main (m : ℕ) (hm : 1 ≤ m) :
    (∀ w : Equiv.Perm (Fin (n_odd m)),
      IsValidOdd m w ↔ w = sigmaPlus m ∨ w = sigmaMinus m) ∧
    Fintype.card { w : Equiv.Perm (Fin (n_odd m)) // IsValidOdd m w } = 2 ∧
    sigmaPlus m ≠ sigmaMinus m ∧
    permReverse (sigmaPlus m) = sigmaMinus m ∧
    permComplement (sigmaPlus m) = sigmaMinus m ∧
    permInverse (sigmaPlus m) = sigmaMinus m ∧
    permRot90 (sigmaPlus m) = sigmaPlus m ∧
    permRot90 (sigmaMinus m) = sigmaMinus m ∧
    (∀ g : SquareSym,
      (applySymPerm g (sigmaPlus m) = sigmaPlus m ∨
       applySymPerm g (sigmaPlus m) = sigmaMinus m) ∧
      (applySymPerm g (sigmaMinus m) = sigmaPlus m ∨
       applySymPerm g (sigmaMinus m) = sigmaMinus m)) ∧
    (∃ g : SquareSym, applySymPerm g (sigmaPlus m) = sigmaMinus m) :=
  ⟨fun w => odd_minimal_prolific_classification m hm w,
   odd_minimal_prolific_card_eq_two m hm,
   odd_symmetries_single_orbit m hm⟩

end MinimalProlific
