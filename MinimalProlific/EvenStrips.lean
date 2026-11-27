/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MinimalProlific.Defs
public import Mathlib.Data.Fintype.Prod

import Mathlib.Tactic

/-!
# Claim B1: Strip Construction for Every Even `k = 2r - 2` (`MinimalProlific.EvenStrips`)

Formalizes Section 3.2 of Track 7-PROLIFIC (`03b_even.md`):
For every `r ≥ 2`, `k = 2r - 2`, `d = 2r`, `N = 2r^2`, `n = N - 1`:
1. Given any `π : Equiv.Perm (Fin (r - 1))`, define the `r`-periodic shift sequence `λ` with
   `λ₀ = 0` and distinct residues mod `r`, and the strip set
   `T(λ) = { i(r, -r) + λ_i(1, 1) + j(r, r) : i, j ∈ ℤ }`.
2. **Claim B1(a):** Distinct points of `T(λ)` are at taxicab distance `≥ 2r` (`stripPt_dist`).
3. **Claim B1(b):** `T(λ)` is `N ℤ^2`-invariant, contains `(0, 0)`, and hits each column and row
   exactly once modulo `N`; hence `P(λ) = T(λ) ∩ [1, n]^2` is the plot of an explicit valid
   permutation `stripPerm r hr π`, and its reverse `permReverse (stripPerm r hr π)` is also valid.
4. **Claim B1(c):** The `2 * (r - 1)!` permutations (`stripPerm` and `permReverse ∘ stripPerm`
   for `π : Equiv.Perm (Fin (r - 1))`) are pairwise distinct, proving
   `2 * (r - 1)! ≤ Fintype.card { w // IsValidEven r w }`.
-/

@[expose] public section

namespace MinimalProlific

open Finset

/-! ## Section 1: Even Parameters and Strip Shifts -/

/-- Torus period `N = 2r^2` for even `k = 2r - 2`. -/
def N_even (r : ℕ) : ℕ := 2 * r ^ 2

/-- Minimal size `n = 2r^2 - 1` for even `k = 2r - 2`. -/
def n_even (r : ℕ) : ℕ := 2 * r ^ 2 - 1

/-- Required separation `d = k + 2 = 2r` for even `k = 2r - 2`. -/
def d_even (r : ℕ) : ℕ := 2 * r

/-- Validity for even `k = 2r - 2` at minimal size `n_even r` (`d_even r = 2r`). -/
def IsValidEven (r : ℕ) (w : Equiv.Perm (Fin (n_even r))) : Prop :=
  IsValidPerm (d_even r) w

instance instDecidablePredIsValidEven (r : ℕ) :
    DecidablePred (IsValidEven r) :=
  instDecidablePredIsValidPerm (n_even r) (d_even r)

theorem N_even_pos {r : ℕ} (hr : 1 ≤ r) : 0 < N_even r := by
  unfold N_even; have := hr; nlinarith

theorem n_even_add_one {r : ℕ} (hr : 1 ≤ r) : n_even r + 1 = N_even r := by
  unfold n_even N_even
  have h1 : 1 ≤ 2 * r ^ 2 := by have := hr; nlinarith
  omega

/-- Residues `λ₀ = 0, λ₁, ..., λ_{r-1} ∈ {0..r-1}` induced by `π : Equiv.Perm (Fin (r - 1))`. -/
def laNat (r : ℕ) (π : Equiv.Perm (Fin (r - 1))) (i : Fin r) : ℕ :=
  if h : i.val = 0 then 0 else (π ⟨i.val - 1, by omega⟩).val + 1

theorem laNat_zero {r : ℕ} (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r - 1))) :
    laNat r π ⟨0, hr⟩ = 0 := by
  simp [laNat]

theorem laNat_lt {r : ℕ} (π : Equiv.Perm (Fin (r - 1))) (i : Fin r) :
    laNat r π i < r := by
  unfold laNat
  split_ifs with h
  · exact i.pos
  · have hpi := (π ⟨i.val - 1, by omega⟩).isLt
    omega

theorem laNat_injective {r : ℕ} (π : Equiv.Perm (Fin (r - 1))) :
    Function.Injective (laNat r π) := by
  intro i₁ i₂ heq
  unfold laNat at heq
  by_cases h1 : i₁.val = 0 <;> by_cases h2 : i₂.val = 0
  · exact Fin.ext (by omega)
  · simp [h1, h2] at heq
  · simp [h1, h2] at heq
  · simp only [h1, h2, ↓reduceDIte] at heq
    have hpi : π ⟨i₁.val - 1, by omega⟩ = π ⟨i₂.val - 1, by omega⟩ :=
      Fin.ext (by omega)
    have hinj := π.injective hpi
    have hval : i₁.val - 1 = i₂.val - 1 := congrArg Fin.val hinj
    exact Fin.ext (by omega)

theorem laNat_eq_iff_perm {r : ℕ} (_hr : 2 ≤ r) {π₁ π₂ : Equiv.Perm (Fin (r - 1))}
    (h : ∀ i : Fin r, laNat r π₁ i = laNat r π₂ i) : π₁ = π₂ := by
  ext j
  have hj := j.isLt
  have h0 := h ⟨j.val + 1, by omega⟩
  unfold laNat at h0
  have hne : j.val + 1 ≠ 0 := by omega
  simp only [hne, ↓reduceDIte] at h0
  have hsub : (⟨j.val + 1 - 1, by omega⟩ : Fin (r - 1)) = j := Fin.ext (by simp)
  rw [hsub] at h0
  exact Nat.succ.inj h0

/-- `r`-periodic integer extension of `laNat r π`. -/
def stripLam (r : ℕ) (π : Equiv.Perm (Fin (r - 1))) (i : ℤ) : ℤ :=
  if hr : 1 ≤ r then
    (laNat r π ⟨(i % (r : ℤ)).toNat, by
      have hr0 : (0 : ℤ) < (r : ℤ) := by omega
      have h1 : 0 ≤ i % (r : ℤ) := Int.emod_nonneg i hr0.ne'
      have h2 : i % (r : ℤ) < (r : ℤ) := Int.emod_lt_of_pos i hr0
      omega⟩ : ℤ)
  else 0

theorem stripLam_fin {r : ℕ} (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r - 1))) (i : Fin r) :
    stripLam r π (i.val : ℤ) = (laNat r π i : ℤ) := by
  unfold stripLam
  simp only [hr, ↓reduceDIte]
  have hi : (i.val : ℤ) % (r : ℤ) = (i.val : ℤ) :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)
  have hidx : (⟨((i.val : ℤ) % (r : ℤ)).toNat, by
      have hr0 : (0 : ℤ) < (r : ℤ) := by omega
      have h1 := Int.emod_nonneg (i.val : ℤ) hr0.ne'
      have h2 := Int.emod_lt_of_pos (i.val : ℤ) hr0
      omega⟩ : Fin r) = i :=
    Fin.ext (by dsimp only; rw [hi, Int.toNat_natCast])
  rw [hidx]

theorem stripLam_add_r {r : ℕ} (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r - 1))) (i : ℤ) :
    stripLam r π (i + (r : ℤ)) = stripLam r π i := by
  unfold stripLam
  simp only [hr, ↓reduceDIte, Int.add_emod_right]

theorem stripLam_add_mul_r {r : ℕ} (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r - 1))) (i k : ℤ) :
    stripLam r π (i + k * (r : ℤ)) = stripLam r π i := by
  unfold stripLam
  simp only [hr, ↓reduceDIte, Int.add_mul_emod_self_right]

theorem stripLam_zero {r : ℕ} (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r - 1))) :
    stripLam r π 0 = 0 := by
  have h := stripLam_fin hr π ⟨0, hr⟩
  rw [laNat_zero hr] at h
  simpa using h

theorem stripLam_bounds {r : ℕ} (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r - 1))) (i : ℤ) :
    0 ≤ stripLam r π i ∧ stripLam r π i < (r : ℤ) := by
  unfold stripLam
  simp only [hr, ↓reduceDIte]
  have hlt := laNat_lt π ⟨(i % (r : ℤ)).toNat, by
    have hr0 : (0 : ℤ) < (r : ℤ) := by omega
    have h1 := Int.emod_nonneg i hr0.ne'
    have h2 := Int.emod_lt_of_pos i hr0
    omega⟩
  omega

/-! ## Section 2: Strip Lattice Set `T(λ)` and Separation (Claim B1(a)) -/

/-- Point `i (r, -r) + λ_i (1, 1) + j (r, r)` of `T(λ)`. -/
def stripPt (r : ℕ) (la : ℤ → ℤ) (i j : ℤ) : ℤ × ℤ :=
  (i * (r : ℤ) + la i + j * (r : ℤ), -(i * (r : ℤ)) + la i + j * (r : ℤ))

/-- Strip set `T(λ) ⊂ ℤ^2`. -/
def stripSet (r : ℕ) (la : ℤ → ℤ) : Set (ℤ × ℤ) :=
  { p | ∃ i j : ℤ, p = stripPt r la i j }

theorem stripPt_diff {r : ℕ} {la : ℤ → ℤ} {i j : ℤ} :
    (stripPt r la i j).1 - (stripPt r la i j).2 = 2 * (r : ℤ) * i := by
  unfold stripPt; ring

theorem stripPt_sum {r : ℕ} {la : ℤ → ℤ} {i j : ℤ} :
    (stripPt r la i j).1 + (stripPt r la i j).2 = 2 * la i + 2 * (r : ℤ) * j := by
  unfold stripPt; ring

/-- **Claim B1(a):** Distinct parameter pairs `(i₁, j₁) ≠ (i₂, j₂)` produce points of `T(λ)` at
taxicab distance at least `2r` (in particular, `stripPt r la` is injective for `r ≥ 1`). -/
theorem stripPt_dist {r : ℕ} (hr : 1 ≤ r) (la : ℤ → ℤ) {i₁ j₁ i₂ j₂ : ℤ}
    (hne : (i₁, j₁) ≠ (i₂, j₂)) :
    (2 * r : ℤ) ≤ taxicabDist (stripPt r la i₁ j₁) (stripPt r la i₂ j₂) := by
  by_cases hi : i₁ = i₂
  · subst hi
    have hj : j₁ ≠ j₂ := fun h => hne (Prod.ext rfl h)
    have hsum := taxicabDist_ge_abs_sum (stripPt r la i₁ j₁) (stripPt r la i₁ j₂)
    have hval : ((stripPt r la i₁ j₁).1 - (stripPt r la i₁ j₂).1) +
        ((stripPt r la i₁ j₁).2 - (stripPt r la i₁ j₂).2) =
        2 * (r : ℤ) * (j₁ - j₂) := by
      unfold stripPt; ring
    rw [hval, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 * (r : ℤ))] at hsum
    have habj : 1 ≤ |j₁ - j₂| := by
      rcases le_or_gt 0 (j₁ - j₂) with h | h
      · rw [abs_of_nonneg h]; omega
      · rw [abs_of_neg h]; omega
    nlinarith
  · have hdiff := taxicabDist_ge_abs_diff (stripPt r la i₁ j₁) (stripPt r la i₂ j₂)
    have hval : ((stripPt r la i₁ j₁).1 - (stripPt r la i₂ j₂).1) -
        ((stripPt r la i₁ j₁).2 - (stripPt r la i₂ j₂).2) =
        2 * (r : ℤ) * (i₁ - i₂) := by
      unfold stripPt; ring
    rw [hval, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 * (r : ℤ))] at hdiff
    have habi : 1 ≤ |i₁ - i₂| := by
      rcases le_or_gt 0 (i₁ - i₂) with h | h
      · rw [abs_of_nonneg h]; omega
      · rw [abs_of_neg h]; omega
    nlinarith

theorem stripPt_injective {r : ℕ} (hr : 1 ≤ r) (la : ℤ → ℤ) :
    Function.Injective (fun p : ℤ × ℤ => stripPt r la p.1 p.2) := by
  intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ heq
  by_contra hne
  have hdist := stripPt_dist hr la hne
  dsimp only at heq
  rw [heq, taxicabDist_self] at hdist
  omega

theorem stripSet_dist {r : ℕ} (hr : 1 ≤ r) (la : ℤ → ℤ) {p q : ℤ × ℤ}
    (hp : p ∈ stripSet r la) (hq : q ∈ stripSet r la) (hpq : p ≠ q) :
    (d_even r : ℤ) ≤ taxicabDist p q := by
  obtain ⟨i₁, j₁, rfl⟩ := hp
  obtain ⟨i₂, j₂, rfl⟩ := hq
  have hne : (i₁, j₁) ≠ (i₂, j₂) := by
    intro h; exact hpq (by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl)
  unfold d_even
  exact_mod_cast stripPt_dist hr la hne

theorem stripPt_shift_torus {r : ℕ} (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r - 1)))
    (i j a b : ℤ) :
    stripPt r (stripLam r π) (i + (a - b) * (r : ℤ)) (j + (a + b) * (r : ℤ)) =
      ((stripPt r (stripLam r π) i j).1 + a * (N_even r : ℤ),
       (stripPt r (stripLam r π) i j).2 + b * (N_even r : ℤ)) := by
  unfold stripPt N_even
  rw [stripLam_add_mul_r hr π i (a - b)]
  ext <;> push_cast <;> ring

theorem stripSet_add_torus {r : ℕ} (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r - 1)))
    {p : ℤ × ℤ} (hp : p ∈ stripSet r (stripLam r π)) (a b : ℤ) :
    (p.1 + a * (N_even r : ℤ), p.2 + b * (N_even r : ℤ)) ∈ stripSet r (stripLam r π) := by
  obtain ⟨i, j, rfl⟩ := hp
  exact ⟨i + (a - b) * (r : ℤ), j + (a + b) * (r : ℤ), (stripPt_shift_torus hr π i j a b).symm⟩

theorem stripSet_zero_mem {r : ℕ} (hr : 1 ≤ r) (π : Equiv.Perm (Fin (r - 1))) :
    (0, 0) ∈ stripSet r (stripLam r π) := by
  refine ⟨0, 0, ?_⟩
  simp [stripPt, stripLam_zero hr π]

/-! ## Section 3: Explicit Strip Permutations and Validity (Claim B1(b)) -/

def colVal (r : ℕ) (hr : 2 ≤ r) (π : Equiv.Perm (Fin (r - 1)))
    (ij : Fin r × Fin (2 * r)) : Fin (N_even r) :=
  ⟨(laNat r π ij.1 + (ij.1.val + ij.2.val) * r) % N_even r,
    Nat.mod_lt _ (N_even_pos (by omega))⟩

def rowVal (r : ℕ) (hr : 2 ≤ r) (π : Equiv.Perm (Fin (r - 1)))
    (ij : Fin r × Fin (2 * r)) : Fin (N_even r) :=
  ⟨(laNat r π ij.1 + (ij.2.val + 2 * r - ij.1.val) * r) % N_even r,
    Nat.mod_lt _ (N_even_pos (by omega))⟩

theorem colVal_injective (r : ℕ) (hr : 2 ≤ r) (π : Equiv.Perm (Fin (r - 1))) :
    Function.Injective (colVal r hr π) := by
  intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  have hval : (laNat r π i₁ + (i₁.val + j₁.val) * r) % N_even r =
      (laNat r π i₂ + (i₂.val + j₂.val) * r) % N_even r := congrArg Fin.val h
  have hdvd : r ∣ N_even r := ⟨2 * r, by unfold N_even; ring⟩
  have hmodr : (laNat r π i₁ + (i₁.val + j₁.val) * r) % r =
      (laNat r π i₂ + (i₂.val + j₂.val) * r) % r := by
    rw [← Nat.mod_mod_of_dvd _ hdvd, hval, Nat.mod_mod_of_dvd _ hdvd]
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (laNat_lt π i₁), Nat.mod_eq_of_lt (laNat_lt π i₂)] at hmodr
  have hi : i₁ = i₂ := laNat_injective π hmodr
  subst hi
  have hz : ((laNat r π i₁ + (i₁.val + j₁.val) * r : ℕ) : ℤ) ≡
      ((laNat r π i₁ + (i₁.val + j₂.val) * r : ℕ) : ℤ) [ZMOD (N_even r : ℤ)] := by
    rw [Int.ModEq, ← Int.natCast_mod, ← Int.natCast_mod, hval]
  have hdvdZ : (N_even r : ℤ) ∣ (((j₁.val : ℤ) - (j₂.val : ℤ)) * (r : ℤ)) := by
    have hsub := Int.ModEq.dvd hz
    have heq : ((laNat r π i₁ + (i₁.val + j₂.val) * r : ℕ) : ℤ) -
        ((laNat r π i₁ + (i₁.val + j₁.val) * r : ℕ) : ℤ) =
        -(((j₁.val : ℤ) - (j₂.val : ℤ)) * (r : ℤ)) := by
      push_cast; ring
    rw [heq] at hsub
    exact dvd_neg.mp hsub
  have hdvd2r : (2 * (r : ℤ)) ∣ ((j₁.val : ℤ) - (j₂.val : ℤ)) := by
    have hN : (N_even r : ℤ) = (2 * (r : ℤ)) * (r : ℤ) := by unfold N_even; push_cast; ring
    rw [hN] at hdvdZ
    exact (mul_dvd_mul_iff_right (by omega : (r : ℤ) ≠ 0)).mp hdvdZ
  obtain ⟨k, hk⟩ := hdvd2r
  have hj1 := j₁.isLt
  have hj2 := j₂.isLt
  have hk0 : k = 0 := by nlinarith
  have hj : j₁ = j₂ := Fin.ext (by nlinarith)
  exact Prod.ext rfl hj

theorem rowVal_injective (r : ℕ) (hr : 2 ≤ r) (π : Equiv.Perm (Fin (r - 1))) :
    Function.Injective (rowVal r hr π) := by
  intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  have hval : (laNat r π i₁ + (j₁.val + 2 * r - i₁.val) * r) % N_even r =
      (laNat r π i₂ + (j₂.val + 2 * r - i₂.val) * r) % N_even r := congrArg Fin.val h
  have hdvd : r ∣ N_even r := ⟨2 * r, by unfold N_even; ring⟩
  have hmodr : (laNat r π i₁ + (j₁.val + 2 * r - i₁.val) * r) % r =
      (laNat r π i₂ + (j₂.val + 2 * r - i₂.val) * r) % r := by
    rw [← Nat.mod_mod_of_dvd _ hdvd, hval, Nat.mod_mod_of_dvd _ hdvd]
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (laNat_lt π i₁), Nat.mod_eq_of_lt (laNat_lt π i₂)] at hmodr
  have hi : i₁ = i₂ := laNat_injective π hmodr
  subst hi
  have hz : ((laNat r π i₁ + (j₁.val + 2 * r - i₁.val) * r : ℕ) : ℤ) ≡
      ((laNat r π i₁ + (j₂.val + 2 * r - i₁.val) * r : ℕ) : ℤ) [ZMOD (N_even r : ℤ)] := by
    rw [Int.ModEq, ← Int.natCast_mod, ← Int.natCast_mod, hval]
  have hi1 : i₁.val ≤ j₁.val + 2 * r := by have := i₁.isLt; omega
  have hi2 : i₁.val ≤ j₂.val + 2 * r := by have := i₁.isLt; omega
  have hdvdZ : (N_even r : ℤ) ∣ (((j₁.val : ℤ) - (j₂.val : ℤ)) * (r : ℤ)) := by
    have hsub := Int.ModEq.dvd hz
    have heq : ((laNat r π i₁ + (j₂.val + 2 * r - i₁.val) * r : ℕ) : ℤ) -
        ((laNat r π i₁ + (j₁.val + 2 * r - i₁.val) * r : ℕ) : ℤ) =
        -(((j₁.val : ℤ) - (j₂.val : ℤ)) * (r : ℤ)) := by
      zify [hi1, hi2]; ring
    rw [heq] at hsub
    exact dvd_neg.mp hsub
  have hdvd2r : (2 * (r : ℤ)) ∣ ((j₁.val : ℤ) - (j₂.val : ℤ)) := by
    have hN : (N_even r : ℤ) = (2 * (r : ℤ)) * (r : ℤ) := by unfold N_even; push_cast; ring
    rw [hN] at hdvdZ
    exact (mul_dvd_mul_iff_right (by omega : (r : ℤ) ≠ 0)).mp hdvdZ
  obtain ⟨k, hk⟩ := hdvd2r
  have hj1 := j₁.isLt
  have hj2 := j₂.isLt
  have hk0 : k = 0 := by nlinarith
  have hj : j₁ = j₂ := Fin.ext (by nlinarith)
  exact Prod.ext rfl hj

noncomputable def colEquiv (r : ℕ) (hr : 2 ≤ r) (π : Equiv.Perm (Fin (r - 1))) :
    Fin r × Fin (2 * r) ≃ Fin (N_even r) :=
  Equiv.ofBijective (colVal r hr π)
    ((Fintype.bijective_iff_injective_and_card (colVal r hr π)).mpr
      ⟨colVal_injective r hr π, by
        simp only [Fintype.card_prod, Fintype.card_fin]
        unfold N_even
        ring⟩)

noncomputable def rowEquiv (r : ℕ) (hr : 2 ≤ r) (π : Equiv.Perm (Fin (r - 1))) :
    Fin r × Fin (2 * r) ≃ Fin (N_even r) :=
  Equiv.ofBijective (rowVal r hr π)
    ((Fintype.bijective_iff_injective_and_card (rowVal r hr π)).mpr
      ⟨rowVal_injective r hr π, by
        simp only [Fintype.card_prod, Fintype.card_fin]
        unfold N_even
        ring⟩)

noncomputable def torusEquiv (r : ℕ) (hr : 2 ≤ r) (π : Equiv.Perm (Fin (r - 1))) :
    Fin (N_even r) ≃ Fin (N_even r) :=
  (colEquiv r hr π).symm.trans (rowEquiv r hr π)

theorem torusEquiv_zero (r : ℕ) (hr : 2 ≤ r) (π : Equiv.Perm (Fin (r - 1))) :
    torusEquiv r hr π ⟨0, N_even_pos (by omega)⟩ = ⟨0, N_even_pos (by omega)⟩ := by
  have hcol0 : colEquiv r hr π (⟨0, by omega⟩, ⟨0, by omega⟩) =
      ⟨0, N_even_pos (by omega)⟩ := by
    ext; simp [colEquiv, colVal, laNat]
  have hrow0 : rowEquiv r hr π (⟨0, by omega⟩, ⟨0, by omega⟩) =
      ⟨0, N_even_pos (by omega)⟩ := by
    ext
    change (laNat r π ⟨0, by omega⟩ + (0 + 2 * r - 0) * r) % N_even r = 0
    have hmul : 0 + (0 + 2 * r - 0) * r = N_even r := by
      simp only [Nat.sub_zero]; unfold N_even; ring
    rw [laNat_zero (by omega), hmul, Nat.mod_self]
  have hsymm : (colEquiv r hr π).symm ⟨0, N_even_pos (by omega)⟩ =
      (⟨0, by omega⟩, ⟨0, by omega⟩) :=
    (Equiv.symm_apply_eq (colEquiv r hr π)).mpr hcol0.symm
  unfold torusEquiv
  rw [Equiv.trans_apply, hsymm, hrow0]

def permSubOneOfZeroFixed {n N : ℕ} (hn : n + 1 = N) (e : Fin N ≃ Fin N)
    (he0 : e ⟨0, by omega⟩ = ⟨0, by omega⟩) : Equiv.Perm (Fin n) where
  toFun x := ⟨(e ⟨x.val + 1, by omega⟩).val - 1, by
    have hne : e ⟨x.val + 1, by omega⟩ ≠ ⟨0, by omega⟩ := by
      intro h
      have hv : x.val + 1 = 0 := congrArg Fin.val (e.injective (h.trans he0.symm))
      omega
    have hlt := (e ⟨x.val + 1, by omega⟩).isLt
    have hvne : (e ⟨x.val + 1, by omega⟩).val ≠ 0 := fun h => hne (Fin.ext h)
    omega⟩
  invFun y := ⟨(e.symm ⟨y.val + 1, by omega⟩).val - 1, by
    have he0' : e.symm ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
      simpa using congrArg e.symm he0.symm
    have hne : e.symm ⟨y.val + 1, by omega⟩ ≠ ⟨0, by omega⟩ := by
      intro h
      have hv : y.val + 1 = 0 := congrArg Fin.val (e.symm.injective (h.trans he0'.symm))
      omega
    have hlt := (e.symm ⟨y.val + 1, by omega⟩).isLt
    have hvne : (e.symm ⟨y.val + 1, by omega⟩).val ≠ 0 := fun h => hne (Fin.ext h)
    omega⟩
  left_inv x := by
    ext
    have hne : e ⟨x.val + 1, by omega⟩ ≠ ⟨0, by omega⟩ := by
      intro h
      have hv : x.val + 1 = 0 := congrArg Fin.val (e.injective (h.trans he0.symm))
      omega
    have hvne : (e ⟨x.val + 1, by omega⟩).val ≠ 0 := fun h => hne (Fin.ext h)
    have hpos : 1 ≤ (e ⟨x.val + 1, by omega⟩).val := Nat.pos_of_ne_zero hvne
    have hsymm : e.symm ⟨(e ⟨x.val + 1, by omega⟩).val - 1 + 1, by omega⟩ =
        ⟨x.val + 1, by omega⟩ := by
      rw [Equiv.symm_apply_eq]
      exact Fin.ext (Nat.sub_add_cancel hpos)
    dsimp only
    rw [hsymm]
    rfl
  right_inv y := by
    ext
    have he0' : e.symm ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
      simpa using congrArg e.symm he0.symm
    have hne : e.symm ⟨y.val + 1, by omega⟩ ≠ ⟨0, by omega⟩ := by
      intro h
      have hv : y.val + 1 = 0 := congrArg Fin.val (e.symm.injective (h.trans he0'.symm))
      omega
    have hvne : (e.symm ⟨y.val + 1, by omega⟩).val ≠ 0 := fun h => hne (Fin.ext h)
    have hpos : 1 ≤ (e.symm ⟨y.val + 1, by omega⟩).val := Nat.pos_of_ne_zero hvne
    have happ : e ⟨(e.symm ⟨y.val + 1, by omega⟩).val - 1 + 1, by omega⟩ =
        ⟨y.val + 1, by omega⟩ := by
      rw [← Equiv.eq_symm_apply]
      exact Fin.ext (Nat.sub_add_cancel hpos)
    dsimp only
    rw [happ]
    rfl

/-- Explicit minimal even `k`-prolific strip permutation `P(λ)` (`r ≥ 2`). -/
noncomputable def stripPerm (r : ℕ) (hr : 2 ≤ r) (π : Equiv.Perm (Fin (r - 1))) :
    Equiv.Perm (Fin (n_even r)) :=
  permSubOneOfZeroFixed (n_even_add_one (by omega)) (torusEquiv r hr π) (torusEquiv_zero r hr π)

/-- Mirror image `(x, y) ↦ (N - x, y)` of `stripPerm`. -/
noncomputable def stripPermMirror (r : ℕ) (hr : 2 ≤ r) (π : Equiv.Perm (Fin (r - 1))) :
    Equiv.Perm (Fin (n_even r)) :=
  permReverse (stripPerm r hr π)

theorem plotPoint_stripPerm_mem_stripSet (r : ℕ) (hr : 2 ≤ r) (π : Equiv.Perm (Fin (r - 1)))
    (x : Fin (n_even r)) :
    plotPoint (stripPerm r hr π) x ∈ stripSet r (stripLam r π) := by
  have hN : n_even r + 1 = N_even r := n_even_add_one (by omega)
  let xN : Fin (N_even r) := ⟨x.val + 1, by omega⟩
  obtain ⟨⟨i, j⟩, hij⟩ := (colEquiv r hr π).surjective xN
  have hcol : (colVal r hr π (i, j)).val = x.val + 1 := by
    have := congrArg Fin.val hij
    simpa [colEquiv, xN] using this
  have htorus : torusEquiv r hr π xN = rowEquiv r hr π (i, j) := by
    unfold torusEquiv
    rw [Equiv.trans_apply, ← hij, Equiv.symm_apply_apply]
  have hne0 : torusEquiv r hr π xN ≠ ⟨0, N_even_pos (by omega)⟩ := by
    intro h
    have hinj := (torusEquiv r hr π).injective (h.trans (torusEquiv_zero r hr π).symm)
    have hv : x.val + 1 = 0 := congrArg Fin.val hinj
    omega
  have hrow : (rowVal r hr π (i, j)).val = (stripPerm r hr π x).val + 1 := by
    unfold stripPerm permSubOneOfZeroFixed
    have hvne : (torusEquiv r hr π xN).val ≠ 0 := fun h => hne0 (Fin.ext h)
    have htval : (torusEquiv r hr π xN).val = (rowVal r hr π (i, j)).val :=
      congrArg Fin.val htorus
    have hpos : 1 ≤ (torusEquiv r hr π xN).val := Nat.pos_of_ne_zero hvne
    change (rowVal r hr π (i, j)).val = (torusEquiv r hr π xN).val - 1 + 1
    rw [Nat.sub_add_cancel hpos, htval]
  have hcolZ : ((x.val : ℤ) + 1) ≡ (stripPt r (stripLam r π) (i.val : ℤ) (j.val : ℤ)).1
      [ZMOD (N_even r : ℤ)] := by
    have h1 : ((x.val + 1 : ℕ) : ℤ) =
        (((laNat r π i + (i.val + j.val) * r) % N_even r : ℕ) : ℤ) := by
      exact_mod_cast hcol.symm
    rw [Nat.cast_add, Nat.cast_one] at h1
    rw [h1, Int.natCast_mod]
    unfold stripPt
    rw [stripLam_fin (by omega) π i]
    have heq : ((laNat r π i + (i.val + j.val) * r : ℕ) : ℤ) =
        (i.val : ℤ) * (r : ℤ) + (laNat r π i : ℤ) + (j.val : ℤ) * (r : ℤ) := by
      push_cast; ring
    rw [heq]
    exact Int.mod_modEq _ _
  have hrowZ : (((stripPerm r hr π x).val : ℤ) + 1) ≡
      (stripPt r (stripLam r π) (i.val : ℤ) (j.val : ℤ)).2 [ZMOD (N_even r : ℤ)] := by
    have h1 : (((stripPerm r hr π x).val + 1 : ℕ) : ℤ) =
        (((laNat r π i + (j.val + 2 * r - i.val) * r) % N_even r : ℕ) : ℤ) := by
      exact_mod_cast hrow.symm
    rw [Nat.cast_add, Nat.cast_one] at h1
    rw [h1, Int.natCast_mod]
    unfold stripPt
    rw [stripLam_fin (by omega) π i]
    have hi : i.val ≤ j.val + 2 * r := by have := i.isLt; omega
    have heq : ((laNat r π i + (j.val + 2 * r - i.val) * r : ℕ) : ℤ) =
        (-(i.val : ℤ) * (r : ℤ) + (laNat r π i : ℤ) + (j.val : ℤ) * (r : ℤ)) +
          1 * (N_even r : ℤ) := by
      zify [hi]; unfold N_even; push_cast; ring
    rw [heq]
    dsimp only
    rw [Int.ModEq, Int.add_mul_emod_self_right, Int.emod_emod]
    congr 1; ring
  obtain ⟨a, ha⟩ := hcolZ.symm.dvd
  obtain ⟨b, hb⟩ := hrowZ.symm.dvd
  have hpt : plotPoint (stripPerm r hr π) x =
      ((stripPt r (stripLam r π) (i.val : ℤ) (j.val : ℤ)).1 + a * (N_even r : ℤ),
       (stripPt r (stripLam r π) (i.val : ℤ) (j.val : ℤ)).2 + b * (N_even r : ℤ)) := by
    unfold plotPoint
    ext <;> dsimp only <;> linarith
  rw [hpt]
  exact stripSet_add_torus (by omega) π ⟨i.val, j.val, rfl⟩ a b

/-- **Claim B1(b):** Both `stripPerm r hr π` and `stripPermMirror r hr π` are valid even
permutations (`breadth ≥ 2r`). -/
theorem stripPerm_isValidEven (r : ℕ) (hr : 2 ≤ r) (π : Equiv.Perm (Fin (r - 1))) :
    IsValidEven r (stripPerm r hr π) := by
  intro x₁ x₂ hne
  apply stripSet_dist (by omega) (stripLam r π)
    (plotPoint_stripPerm_mem_stripSet r hr π x₁)
    (plotPoint_stripPerm_mem_stripSet r hr π x₂)
  intro heq
  exact hne (plotPoint_injective _ heq)

theorem stripPermMirror_isValidEven (r : ℕ) (hr : 2 ≤ r) (π : Equiv.Perm (Fin (r - 1))) :
    IsValidEven r (stripPermMirror r hr π) :=
  isValidPerm_permReverse (stripPerm_isValidEven r hr π)

/-! ## Section 4: Pairwise Distinctness and Lower Bound `2 * (r - 1)!` (Claim B1(c)) -/

private theorem mem_stripSet_iff_torus_of_stripPerm (r : ℕ) (hr : 2 ≤ r)
    (π : Equiv.Perm (Fin (r - 1))) (p : ℤ × ℤ) :
    p ∈ stripSet r (stripLam r π) ↔
      ∃ q ∈ insert (0, 0) (plotSet (stripPerm r hr π)),
        (N_even r : ℤ) ∣ (p.1 - q.1) ∧ (N_even r : ℤ) ∣ (p.2 - q.2) := by
  have hNpos : (0 : ℤ) < (N_even r : ℤ) := by exact_mod_cast N_even_pos (by omega)
  have hN1 : n_even r + 1 = N_even r := n_even_add_one (by omega)
  constructor
  · rintro ⟨i, j, rfl⟩
    let i0 : ℤ := i % (r : ℤ)
    let qi : ℤ := i / (r : ℤ)
    have hi_decomp : i0 + (r : ℤ) * qi = i := Int.emod_add_mul_ediv i (r : ℤ)
    have hi0_b : 0 ≤ i0 ∧ i0 < (r : ℤ) :=
      ⟨Int.emod_nonneg i (by omega), Int.emod_lt_of_pos i (by omega)⟩
    let j0 : ℤ := (j + qi * (r : ℤ)) % (2 * (r : ℤ))
    have hj0_b : 0 ≤ j0 ∧ j0 < 2 * (r : ℤ) :=
      ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
    let iFin : Fin r := ⟨i0.toNat, by omega⟩
    let jFin : Fin (2 * r) := ⟨j0.toNat, by omega⟩
    have hlam : stripLam r π i = (laNat r π iFin : ℤ) := by
      unfold stripLam
      simp [show 1 ≤ r by omega, iFin, i0]
    have h2r : ∃ t : ℤ, j0 - (j + qi * (r : ℤ)) = 2 * (r : ℤ) * t := by
      have := Int.emod_add_mul_ediv (j + qi * (r : ℤ)) (2 * (r : ℤ))
      exact ⟨-((j + qi * (r : ℤ)) / (2 * (r : ℤ))), by linarith⟩
    obtain ⟨t, ht⟩ := h2r
    have hiF : (iFin.val : ℤ) = i0 := by dsimp [iFin]; omega
    have hjF : (jFin.val : ℤ) = j0 := by dsimp [jFin]; omega
    have hN : (N_even r : ℤ) = 2 * (r : ℤ) * (r : ℤ) := by unfold N_even; push_cast; ring
    have hmod_x : (stripPt r (stripLam r π) i j).1 ≡
        ((colVal r hr π (iFin, jFin)).val : ℤ) [ZMOD (N_even r : ℤ)] := by
      unfold stripPt colVal
      dsimp only
      rw [hlam, Int.natCast_mod]
      refine Int.ModEq.trans ?_ (Int.mod_modEq _ _).symm
      rw [Int.modEq_iff_dvd]
      refine ⟨t, ?_⟩
      push_cast
      rw [hiF, hjF, hN]
      linear_combination (r : ℤ) * ht + (r : ℤ) * hi_decomp
    have hmod_y : (stripPt r (stripLam r π) i j).2 ≡
        ((rowVal r hr π (iFin, jFin)).val : ℤ) [ZMOD (N_even r : ℤ)] := by
      unfold stripPt rowVal
      dsimp only
      rw [hlam, Int.natCast_mod]
      refine Int.ModEq.trans ?_ (Int.mod_modEq _ _).symm
      rw [Int.modEq_iff_dvd]
      have hi_le : iFin.val ≤ jFin.val + 2 * r := by have := iFin.isLt; omega
      refine ⟨t + 1 + qi, ?_⟩
      zify [hi_le]
      rw [hiF, hjF, hN]
      linear_combination (r : ℤ) * ht - (r : ℤ) * hi_decomp
    by_cases hc0 : colVal r hr π (iFin, jFin) = ⟨0, N_even_pos (by omega)⟩
    · have h00 : (iFin, jFin) = (⟨0, by omega⟩, ⟨0, by omega⟩) := by
        apply colVal_injective r hr π
        rw [hc0]
        ext; simp [colVal, laNat]
      have hr0 : rowVal r hr π (iFin, jFin) = ⟨0, N_even_pos (by omega)⟩ := by
        rw [h00]; ext
        change (laNat r π ⟨0, by omega⟩ + (0 + 2 * r - 0) * r) % N_even r = 0
        have hmul : 0 + (0 + 2 * r - 0) * r = N_even r := by
          simp only [Nat.sub_zero]; unfold N_even; ring
        rw [laNat_zero (by omega), hmul, Nat.mod_self]
      rw [hc0] at hmod_x
      rw [hr0] at hmod_y
      refine ⟨(0, 0), Set.mem_insert _ _, ?_, ?_⟩
      · simpa using hmod_x.symm.dvd
      · simpa using hmod_y.symm.dvd
    · have hcpos : 1 ≤ (colVal r hr π (iFin, jFin)).val := by
        have hne : (colVal r hr π (iFin, jFin)).val ≠ 0 := fun h => hc0 (Fin.ext h)
        omega
      have hclt := (colVal r hr π (iFin, jFin)).isLt
      let x : Fin (n_even r) := ⟨(colVal r hr π (iFin, jFin)).val - 1, by omega⟩
      have hxN : (⟨x.val + 1, by omega⟩ : Fin (N_even r)) = colEquiv r hr π (iFin, jFin) := by
        ext; dsimp [x, colEquiv]; omega
      have htorus : torusEquiv r hr π ⟨x.val + 1, by omega⟩ = rowEquiv r hr π (iFin, jFin) := by
        unfold torusEquiv
        rw [Equiv.trans_apply, hxN, Equiv.symm_apply_apply]
      have hne0 : torusEquiv r hr π ⟨x.val + 1, by omega⟩ ≠ ⟨0, N_even_pos (by omega)⟩ := by
        intro h
        have hv : x.val + 1 = 0 :=
          congrArg Fin.val ((torusEquiv r hr π).injective (h.trans (torusEquiv_zero r hr π).symm))
        omega
      have hrow_eq : ((stripPerm r hr π x).val : ℤ) + 1 = ((rowVal r hr π (iFin, jFin)).val : ℤ) := by
        unfold stripPerm permSubOneOfZeroFixed
        have hvne : (torusEquiv r hr π ⟨x.val + 1, by omega⟩).val ≠ 0 := fun h => hne0 (Fin.ext h)
        have hpos : 1 ≤ (torusEquiv r hr π ⟨x.val + 1, by omega⟩).val := Nat.pos_of_ne_zero hvne
        have htval : (torusEquiv r hr π ⟨x.val + 1, by omega⟩).val =
            (rowVal r hr π (iFin, jFin)).val := congrArg Fin.val htorus
        have hxval : (((torusEquiv r hr π ⟨x.val + 1, by omega⟩).val - 1 : ℕ) : ℤ) + 1 =
            ((torusEquiv r hr π ⟨x.val + 1, by omega⟩).val : ℤ) := by
          exact_mod_cast Nat.sub_add_cancel hpos
        change ((((torusEquiv r hr π ⟨x.val + 1, by omega⟩).val - 1 : ℕ) : ℤ) + 1) =
            ((rowVal r hr π (iFin, jFin)).val : ℤ)
        rw [hxval, htval]
      have hx_eq : ((x.val : ℤ) + 1) = ((colVal r hr π (iFin, jFin)).val : ℤ) := by
        dsimp [x]; omega
      refine ⟨plotPoint (stripPerm r hr π) x, Set.mem_insert_of_mem _ ⟨x, rfl⟩, ?_, ?_⟩
      · unfold plotPoint; dsimp only; rw [hx_eq]; exact hmod_x.symm.dvd
      · unfold plotPoint; dsimp only; rw [hrow_eq]; exact hmod_y.symm.dvd
  · rintro ⟨q, hq, ⟨a, ha⟩, ⟨b, hb⟩⟩
    have hp : p = (q.1 + a * (N_even r : ℤ), q.2 + b * (N_even r : ℤ)) := by
      ext <;> dsimp only <;> linarith
    rw [hp]
    apply stripSet_add_torus (by omega) π
    rcases Set.mem_insert_iff.mp hq with rfl | ⟨x, rfl⟩
    · exact stripSet_zero_mem (by omega) π
    · exact plotPoint_stripPerm_mem_stripSet r hr π x

private theorem stripSet_eq_imp_perm_eq {r : ℕ} (hr : 2 ≤ r)
    {π₁ π₂ : Equiv.Perm (Fin (r - 1))}
    (hset : stripSet r (stripLam r π₁) = stripSet r (stripLam r π₂)) : π₁ = π₂ := by
  apply laNat_eq_iff_perm hr
  intro i
  have hmem : stripPt r (stripLam r π₁) (i.val : ℤ) 0 ∈ stripSet r (stripLam r π₂) := by
    rw [← hset]; exact ⟨i.val, 0, rfl⟩
  obtain ⟨i', j', heq⟩ := hmem
  have hdiff := congrArg (fun p : ℤ × ℤ => p.1 - p.2) heq
  simp only [stripPt_diff] at hdiff
  have hi' : (i.val : ℤ) = i' := by nlinarith
  subst hi'
  have hsum := congrArg (fun p : ℤ × ℤ => p.1 + p.2) heq
  simp only [stripPt_sum, mul_zero, add_zero] at hsum
  rw [stripLam_fin (by omega) π₁ i, stripLam_fin (by omega) π₂ i] at hsum
  have h1 := laNat_lt π₁ i
  have h2 := laNat_lt π₂ i
  have hj0 : j' = 0 := by nlinarith
  nlinarith

private theorem stripSet_ne_mirror {r : ℕ} (hr : 2 ≤ r)
    (π₁ π₂ : Equiv.Perm (Fin (r - 1))) :
    stripPerm r hr π₁ ≠ stripPermMirror r hr π₂ := by
  intro heq
  have hr1 : 1 ≤ r := by omega
  have hrr : ((r : ℤ), (r : ℤ)) ∈ stripSet r (stripLam r π₁) := by
    refine ⟨0, 1, ?_⟩
    simp [stripPt, stripLam_zero hr1 π₁]
  rw [mem_stripSet_iff_torus_of_stripPerm r hr π₁] at hrr
  obtain ⟨q, hq, hx, hy⟩ := hrr
  have hq_mir : q ∈ insert (0, 0) (plotSet (stripPermMirror r hr π₂)) := by
    rwa [← heq]
  have hN : ((n_even r : ℤ) + 1) = (N_even r : ℤ) := by
    exact_mod_cast n_even_add_one hr1
  have hmir_pt : ptFlipX (N_even r : ℤ) q ∈ insert (0, 0) (plotSet (stripPerm r hr π₂)) := by
    rcases Set.mem_insert_iff.mp hq_mir with rfl | ⟨x, rfl⟩
    · exfalso
      have hx0 : (N_even r : ℤ) ∣ (r : ℤ) := by simpa using hx
      have hle := Int.le_of_dvd (by omega) hx0
      unfold N_even at hle
      push_cast at hle
      nlinarith
    · refine Set.mem_insert_of_mem _ ⟨Fin.rev x, ?_⟩
      unfold stripPermMirror
      have hpx : plotPoint (permReverse (stripPerm r hr π₂)) x =
          ptFlipX (N_even r : ℤ) (plotPoint (stripPerm r hr π₂) (Fin.rev x)) := by
        simpa [Fin.rev_rev, hN] using plotPoint_permReverse (stripPerm r hr π₂) (Fin.rev x)
      rw [hpx]
      unfold ptFlipX
      ext <;> simp
  have hmir_in : ptFlipX (N_even r : ℤ) ((r : ℤ), (r : ℤ)) ∈ stripSet r (stripLam r π₂) := by
    rw [mem_stripSet_iff_torus_of_stripPerm r hr π₂]
    refine ⟨ptFlipX (N_even r : ℤ) q, hmir_pt, ?_, ?_⟩
    · unfold ptFlipX
      have heq1 : ((N_even r : ℤ) - (r : ℤ)) - ((N_even r : ℤ) - q.1) = -(r - q.1) := by ring
      rw [heq1]
      exact dvd_neg.mpr hx
    · exact hy
  obtain ⟨i2, j2, h2⟩ := hmir_in
  have hN2r : ((N_even r : ℤ), 2 * (r : ℤ)) ∈ stripSet r (stripLam r π₂) := by
    refine ⟨i2, j2 + 1, ?_⟩
    have hstep : stripPt r (stripLam r π₂) i2 (j2 + 1) =
        ((stripPt r (stripLam r π₂) i2 j2).1 + (r : ℤ),
         (stripPt r (stripLam r π₂) i2 j2).2 + (r : ℤ)) := by
      unfold stripPt
      ext <;> dsimp only <;> ring
    rw [hstep, ← h2]
    unfold ptFlipX
    ext <;> dsimp only <;> ring
  have h02r : ((0 : ℤ), 2 * (r : ℤ)) ∈ stripSet r (stripLam r π₂) := by
    have hsh := stripSet_add_torus hr1 π₂ hN2r (-1) 0
    simpa using hsh
  obtain ⟨i3, j3, h3⟩ := h02r
  have hdiff := congrArg (fun p : ℤ × ℤ => p.1 - p.2) h3
  simp only [stripPt_diff] at hdiff
  have hi3 : i3 = -1 := by nlinarith
  subst hi3
  have hx3 := congrArg Prod.fst h3
  dsimp only [stripPt] at hx3
  have hlam0 : stripLam r π₂ (-1) = 0 := by
    have hb := stripLam_bounds hr1 π₂ (-1)
    have hdvd : (r : ℤ) ∣ stripLam r π₂ (-1) := ⟨1 - j3, by linarith⟩
    rcases hdvd with ⟨k, hk⟩
    have hk0 : k = 0 := by nlinarith
    nlinarith
  unfold stripLam at hlam0
  simp only [hr1, ↓reduceDIte] at hlam0
  have hmod : (-1 : ℤ) % (r : ℤ) = (r : ℤ) - 1 := by
    have h1 : (-1 : ℤ) = ((r : ℤ) - 1) + (r : ℤ) * (-1) := by ring
    rw [h1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  have hinj : (⟨((-1 : ℤ) % (r : ℤ)).toNat, by omega⟩ : Fin r) = ⟨0, hr1⟩ := by
    apply laNat_injective π₂
    rw [laNat_zero hr1]
    exact_mod_cast hlam0
  have hval := congrArg Fin.val hinj
  dsimp only at hval
  rw [hmod] at hval
  omega

/-- The `2 * (r - 1)!` distinct valid strip permutations (`stripPerm` and `stripPermMirror`). -/
noncomputable def stripFamilyMap (r : ℕ) (hr : 2 ≤ r) (x : Bool × Equiv.Perm (Fin (r - 1))) :
    { w : Equiv.Perm (Fin (n_even r)) // IsValidEven r w } :=
  ⟨if x.1 then stripPermMirror r hr x.2 else stripPerm r hr x.2, by
    cases hx : x.1
    · simpa using stripPerm_isValidEven r hr x.2
    · simpa using stripPermMirror_isValidEven r hr x.2⟩

theorem stripFamilyMap_injective (r : ℕ) (hr : 2 ≤ r) :
    Function.Injective (stripFamilyMap r hr) := by
  rintro ⟨b₁, π₁⟩ ⟨b₂, π₂⟩ h
  have hw : (if b₁ then stripPermMirror r hr π₁ else stripPerm r hr π₁) =
      (if b₂ then stripPermMirror r hr π₂ else stripPerm r hr π₂) :=
    congrArg Subtype.val h
  cases b₁ <;> cases b₂
  · simp only [Bool.false_eq_true, ↓reduceIte] at hw
    have hset : stripSet r (stripLam r π₁) = stripSet r (stripLam r π₂) := by
      ext p
      rw [mem_stripSet_iff_torus_of_stripPerm r hr π₁,
        mem_stripSet_iff_torus_of_stripPerm r hr π₂, hw]
    exact congrArg (Prod.mk false) (stripSet_eq_imp_perm_eq hr hset)
  · simp only [Bool.false_eq_true, ↓reduceIte] at hw
    exact absurd hw (stripSet_ne_mirror hr π₁ π₂)
  · simp only [Bool.false_eq_true, ↓reduceIte] at hw
    exact absurd hw.symm (stripSet_ne_mirror hr π₂ π₁)
  · simp only [↓reduceIte] at hw
    have hperm : stripPerm r hr π₁ = stripPerm r hr π₂ := by
      refine Equiv.ext fun i => ?_
      have hi := Equiv.congr_fun hw (Fin.rev i)
      simpa [stripPermMirror, permReverse] using hi
    have hset : stripSet r (stripLam r π₁) = stripSet r (stripLam r π₂) := by
      ext p
      rw [mem_stripSet_iff_torus_of_stripPerm r hr π₁,
        mem_stripSet_iff_torus_of_stripPerm r hr π₂, hperm]
    exact congrArg (Prod.mk true) (stripSet_eq_imp_perm_eq hr hset)

/-- **Claim B1(c) & Headline Lower Bound:** For every `r ≥ 2`, there are at least `2 * (r - 1)!`
valid minimal permutations at even `k = 2r - 2` (`n_even r = 2r^2 - 1`, `d_even r = 2r`). -/
theorem even_strip_lower_bound (r : ℕ) (hr : 2 ≤ r) :
    2 * Nat.factorial (r - 1) ≤
      Fintype.card { w : Equiv.Perm (Fin (n_even r)) // IsValidEven r w } := by
  have hle := Fintype.card_le_of_injective (stripFamilyMap r hr) (stripFamilyMap_injective r hr)
  simpa [Fintype.card_bool, Fintype.card_perm, Fintype.card_fin] using hle

end MinimalProlific
