module

public import MinimalProlific.OddTents

import Mathlib.Tactic

/-!
# Steps 6–8 of Theorem A (`MinimalProlific.LeeLattice`)

Formalizes Steps 6, 7, and 8 of `03a_theorem_odd.md` for every `m ≥ 1`:
- **Step 6 (`claim6_torus_tiling`)**: For any valid `w : Equiv.Perm (Fin (n_odd m))`,
  `T = (plotSet w ∪ {(0, 0)}) + N ℤ^2` is a radius-`m` Lee tiling of `ℤ^2` containing `(0, 0)`.
- **Step 7 (`claim7_lee_tiling_classification`)**: Every radius-`m` Lee tiling `T ⊆ ℤ^2` containing
  `(0, 0)` equals either `LambdaPlus m = ⟨(m + 1, m), (-m, m + 1)⟩` or its mirror `LambdaMinus m`.
- **Step 8 (`LambdaPlus_eq_mod`, `LambdaMinus_eq_mod`, `sigmaPlus_isValidOdd`,
  `sigmaMinus_isValidOdd`)**: Algebraic characterization `Λ⁺ = {(x, y) | N ∣ (y - dx)}` and
  `Λ⁻ = {(x, y) | N ∣ (y + dx)}`, converse validity of `sigmaPlus m` and `sigmaMinus m`,
  and exact classification of valid odd permutations.
-/

@[expose] public section

namespace MinimalProlific

open Finset

/-! ## Section 1: Lee Tilings and Step 6 (Claim 6) -/

/-- A subset `T ⊆ ℤ × ℤ` is a radius-`m` Lee tiling of `ℤ^2` iff the Lee spheres `S(c)` for
`c ∈ T` are pairwise disjoint and cover `ℤ^2`. -/
def IsLeeTiling (m : ℕ) (T : Set (ℤ × ℤ)) : Prop :=
  (∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → Disjoint (leeSphere m c) (leeSphere m c')) ∧
  (∀ z : ℤ × ℤ, ∃ c ∈ T, z ∈ leeSphere m c)

/-- Torus lift `T = (P ∪ {O}) + N ℤ^2` of a permutation plot `w`. -/
def torusCenters (m : ℕ) (w : Equiv.Perm (Fin (n_odd m))) : Set (ℤ × ℤ) :=
  { c | ∃ q ∈ insert (0, 0) (plotSet w), ∃ a b : ℤ,
    c = (q.1 + a * (N_odd m : ℤ), q.2 + b * (N_odd m : ℤ)) }

theorem zero_mem_torusCenters (m : ℕ) (w : Equiv.Perm (Fin (n_odd m))) :
    (0, 0) ∈ torusCenters m w :=
  ⟨(0, 0), Set.mem_insert _ _, 0, 0, by simp⟩

theorem torusCenters_add_torus {m : ℕ} {w : Equiv.Perm (Fin (n_odd m))} {c : ℤ × ℤ}
    (hc : c ∈ torusCenters m w) (a b : ℤ) :
    (c.1 + a * (N_odd m : ℤ), c.2 + b * (N_odd m : ℤ)) ∈ torusCenters m w := by
  obtain ⟨q, hq, a0, b0, rfl⟩ := hc
  exact ⟨q, hq, a0 + a, b0 + b, by ext <;> dsimp only <;> ring⟩

private theorem torusCenters_permInverse {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) (c : ℤ × ℤ) :
    c ∈ torusCenters m (permInverse w) ↔ ptTranspose c ∈ torusCenters m w := by
  constructor
  · rintro ⟨q, hq, a, b, rfl⟩
    refine ⟨ptTranspose q, ?_, b, a, ?_⟩
    · rcases Set.mem_insert_iff.mp hq with rfl | ⟨i, rfl⟩
      · exact Set.mem_insert _ _
      · refine Set.mem_insert_of_mem _ ⟨w.symm i, ?_⟩
        have h := plotPoint_permInverse w (w.symm i)
        rw [Equiv.apply_symm_apply] at h
        rw [h]; rfl
    · unfold ptTranspose; ext <;> rfl
  · rintro ⟨q, hq, a, b, hceq⟩
    refine ⟨ptTranspose q, ?_, b, a, ?_⟩
    · rcases Set.mem_insert_iff.mp hq with rfl | ⟨i, rfl⟩
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨w i, plotPoint_permInverse w i⟩
    · have h1 := congrArg Prod.fst hceq
      have h2 := congrArg Prod.snd hceq
      unfold ptTranspose at h1 h2 ⊢
      ext <;> dsimp only at h1 h2 ⊢ <;> linarith

private theorem torusCenters_cover_col_central {m : ℕ} (hm : 1 ≤ m)
    {w : Equiv.Perm (Fin (n_odd m))} (hw : IsValidOdd m w)
    {x y : ℤ} (hx : x ∈ centralSet m)
    (hy : y = 0 ∨ (1 ≤ y ∧ y ≤ (n_odd m : ℤ) ∧ ¬ isCovered m w (x, y))) :
    ∃ c ∈ torusCenters m w, (x, y) ∈ leeSphere m c := by
  have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  rcases central_mem_top_or_bot hm hw hx with htop | hbot
  · obtain ⟨t, ht⟩ := htop
    have hov := overhang_eq_of_mem_topSupport hm hw ht
    have hsup := mem_topSupport_iff.mp ht
    let c : ℤ × ℤ := (topCol m hm w t, -1 - (t.val : ℤ))
    have hc_mem : c ∈ torusCenters m w := by
      refine ⟨(topCol m hm w t, (n_odd m : ℤ) - (t.val : ℤ)),
        Set.mem_insert_of_mem _ ⟨w.symm (topRowIdx m hm t), ?_⟩, 0, -1, ?_⟩
      · unfold plotPoint topCol
        rw [Equiv.apply_symm_apply]
        unfold topRowIdx
        have h2m := two_mul_m_le_n_odd hm
        have hlt := t.isLt
        ext <;> dsimp only <;> omega
      · ext <;> dsimp only [c] <;> omega
    refine ⟨c, hc_mem, ?_⟩
    change taxicabDist c (x, y) ≤ (m : ℤ)
    unfold taxicabDist c
    dsimp only
    rw [abs_sub_comm (topCol m hm w t) x]
    unfold tentHeight at hsup hov
    rcases hy with rfl | ⟨hy1, _, hnc⟩
    · have hab : |-1 - (t.val : ℤ) - 0| = 1 + (t.val : ℤ) := by rw [abs_of_neg (by omega)]; ring
      rw [hab]; omega
    · have h5 := (claim5_central_col_holes hm hw hx).1 ⟨t, ht⟩
      have hymem : y ∈ holesInCol m w x := mem_holesInCol.mpr ⟨hy1, by omega, hnc⟩
      rw [h5, Finset.mem_Icc] at hymem
      have hab : |-1 - (t.val : ℤ) - y| = 1 + (t.val : ℤ) + y := by rw [abs_of_neg (by omega)]; ring
      rw [hab]; omega
  · obtain ⟨t, ht⟩ := hbot
    have hov := overhang_eq_of_mem_botSupport hm hw ht
    have hsup := mem_botSupport_iff.mp ht
    have hpt : (botCol m hm w t, 1 + (t.val : ℤ)) ∈ plotSet w := by
      refine ⟨w.symm (botRowIdx m hm t), ?_⟩
      unfold plotPoint botCol
      rw [Equiv.apply_symm_apply]
      unfold botRowIdx
      ext <;> dsimp only <;> ring
    rcases hy with rfl | ⟨hy1, hyn, hnc⟩
    · refine ⟨(botCol m hm w t, 1 + (t.val : ℤ)),
        ⟨_, Set.mem_insert_of_mem _ hpt, 0, 0, by simp⟩, ?_⟩
      change taxicabDist (botCol m hm w t, 1 + (t.val : ℤ)) (x, 0) ≤ (m : ℤ)
      unfold taxicabDist
      dsimp only
      rw [abs_sub_comm (botCol m hm w t) x, sub_zero]
      have hab : |1 + (t.val : ℤ)| = 1 + (t.val : ℤ) := abs_of_pos (by omega)
      rw [hab]
      unfold tentHeight at hsup
      omega
    · refine ⟨(botCol m hm w t, 1 + (t.val : ℤ) + (N_odd m : ℤ)),
        ⟨_, Set.mem_insert_of_mem _ hpt, 0, 1, by simp⟩, ?_⟩
      change taxicabDist (botCol m hm w t, 1 + (t.val : ℤ) + (N_odd m : ℤ)) (x, y) ≤ (m : ℤ)
      unfold taxicabDist
      dsimp only
      rw [abs_sub_comm (botCol m hm w t) x]
      have h5 := (claim5_central_col_holes hm hw hx).2 ⟨t, ht⟩
      have hymem : y ∈ holesInCol m w x := mem_holesInCol.mpr ⟨hy1, hyn, hnc⟩
      rw [h5, Finset.mem_Icc] at hymem
      unfold tentHeight at hsup hov
      have hab : |1 + (t.val : ℤ) + (N_odd m : ℤ) - y| = 1 + (t.val : ℤ) + (N_odd m : ℤ) - y :=
        abs_of_nonneg (by omega)
      rw [hab]
      omega

private theorem torusCenters_cover_fundamental {m : ℕ} (hm : 1 ≤ m)
    {w : Equiv.Perm (Fin (n_odd m))} (hw : IsValidOdd m w)
    {x y : ℤ} (hx0 : 0 ≤ x) (hxn : x ≤ (n_odd m : ℤ))
    (hy0 : 0 ≤ y) (hyn : y ≤ (n_odd m : ℤ)) :
    ∃ c ∈ torusCenters m w, (x, y) ∈ leeSphere m c := by
  have h2m := two_mul_m_le_n_odd hm
  have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  -- y = 0
  by_cases hyz : y = 0
  · subst hyz
    by_cases hxm : x ≤ (m : ℤ)
    · refine ⟨(0, 0), zero_mem_torusCenters m w, ?_⟩
      change taxicabDist (0, 0) (x, 0) ≤ (m : ℤ)
      unfold taxicabDist; simp; rw [abs_of_nonneg hx0]; exact hxm
    · by_cases hxR : (N_odd m : ℤ) - (m : ℤ) ≤ x
      · refine ⟨((N_odd m : ℤ), 0),
          by simpa using torusCenters_add_torus (zero_mem_torusCenters m w) 1 0, ?_⟩
        change taxicabDist ((N_odd m : ℤ), 0) (x, 0) ≤ (m : ℤ)
        unfold taxicabDist; simp; rw [abs_of_nonneg (by omega)]; omega
      · have hxC : x ∈ centralSet m := mem_centralSet_iff.mpr ⟨by omega, by omega⟩
        exact torusCenters_cover_col_central hm hw hxC (Or.inl rfl)
  -- x = 0
  by_cases hxz : x = 0
  · subst hxz
    by_cases hym : y ≤ (m : ℤ)
    · refine ⟨(0, 0), zero_mem_torusCenters m w, ?_⟩
      change taxicabDist (0, 0) (0, y) ≤ (m : ℤ)
      unfold taxicabDist; simp; rw [abs_of_nonneg hy0]; exact hym
    · by_cases hyR : (N_odd m : ℤ) - (m : ℤ) ≤ y
      · refine ⟨(0, (N_odd m : ℤ)),
          by simpa using torusCenters_add_torus (zero_mem_torusCenters m w) 0 1, ?_⟩
        change taxicabDist (0, (N_odd m : ℤ)) (0, y) ≤ (m : ℤ)
        unfold taxicabDist; simp; rw [abs_of_nonneg (by omega)]; omega
      · have hyC : y ∈ centralSet m := mem_centralSet_iff.mpr ⟨by omega, by omega⟩
        obtain ⟨c, hc, hsph⟩ := torusCenters_cover_col_central hm (isValidPerm_permInverse hw)
          hyC (Or.inl rfl)
        refine ⟨ptTranspose c, (torusCenters_permInverse w c).mp hc, ?_⟩
        change taxicabDist (ptTranspose c) (0, y) ≤ (m : ℤ)
        rw [taxicabDist_ptTranspose_left]
        exact hsph
  -- 1 ≤ x ≤ n, 1 ≤ y ≤ n
  by_cases hcov : isCovered m w (x, y)
  · obtain ⟨i, hi⟩ := hcov
    exact ⟨plotPoint w i, ⟨_, Set.mem_insert_of_mem _ ⟨i, rfl⟩, 0, 0, by simp⟩, hi⟩
  · by_cases hxC : x ∈ centralSet m
    · by_cases hyC : y ∈ centralSet m
      · exact absurd (claim4_central_box_covered hm hw hxC hyC) hcov
      · exact torusCenters_cover_col_central hm hw hxC (Or.inr ⟨by omega, hyn, hcov⟩)
    · by_cases hyC : y ∈ centralSet m
      · have hcov_inv : ¬ isCovered m (permInverse w) (y, x) := by
          rw [isCovered_permInverse]; exact hcov
        obtain ⟨c, hc, hsph⟩ := torusCenters_cover_col_central hm (isValidPerm_permInverse hw)
          hyC (Or.inr ⟨by omega, hxn, hcov_inv⟩)
        refine ⟨ptTranspose c, (torusCenters_permInverse w c).mp hc, ?_⟩
        change taxicabDist (ptTranspose c) (x, y) ≤ (m : ℤ)
        rw [taxicabDist_ptTranspose_left]
        exact hsph
      · -- Four corner squares
        rw [mem_centralSet_iff] at hxC hyC
        have hx_lr : x ≤ (m : ℤ) ∨ (N_odd m : ℤ) - (m : ℤ) ≤ x := by omega
        have hy_lr : y ≤ (m : ℤ) ∨ (N_odd m : ℤ) - (m : ℤ) ≤ y := by omega
        rcases hx_lr with hxm | hxR <;> rcases hy_lr with hym | hyR
        · have hle := (claim3a_corner_square_00 hm hw (by omega) hxm (by omega) hym).mp
            ⟨by omega, hxn, by omega, hyn, hcov⟩
          refine ⟨(0, 0), zero_mem_torusCenters m w, ?_⟩
          change taxicabDist (0, 0) (x, y) ≤ (m : ℤ)
          unfold taxicabDist; dsimp only
          rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]
          omega
        · have hhole_c : isHole m (permComplement w) (x, (N_odd m : ℤ) - y) := by
            rw [isHole_permComplement]
            unfold ptFlipY
            simpa using show isHole m w (x, y) from ⟨by omega, hxn, by omega, hyn, hcov⟩
          have hle := (claim3a_corner_square_00 hm (isValidPerm_permComplement hw)
            (by omega) hxm (by omega) (by omega)).mp hhole_c
          refine ⟨(0, (N_odd m : ℤ)),
            by simpa using torusCenters_add_torus (zero_mem_torusCenters m w) 0 1, ?_⟩
          change taxicabDist (0, (N_odd m : ℤ)) (x, y) ≤ (m : ℤ)
          unfold taxicabDist; dsimp only
          rw [abs_of_nonpos (by omega), abs_of_nonneg (by omega)]
          omega
        · have hhole_r : isHole m (permReverse w) ((N_odd m : ℤ) - x, y) := by
            rw [isHole_permReverse]
            unfold ptFlipX
            simpa using show isHole m w (x, y) from ⟨by omega, hxn, by omega, hyn, hcov⟩
          have hle := (claim3a_corner_square_00 hm (isValidPerm_permReverse hw)
            (by omega) (by omega) (by omega) hym).mp hhole_r
          refine ⟨((N_odd m : ℤ), 0),
            by simpa using torusCenters_add_torus (zero_mem_torusCenters m w) 1 0, ?_⟩
          change taxicabDist ((N_odd m : ℤ), 0) (x, y) ≤ (m : ℤ)
          unfold taxicabDist; dsimp only
          rw [abs_of_nonneg (by omega), abs_of_nonpos (by omega)]
          omega
        · have hhole_rc : isHole m (permReverse (permComplement w))
              ((N_odd m : ℤ) - x, (N_odd m : ℤ) - y) := by
            rw [isHole_permReverse, isHole_permComplement]
            unfold ptFlipX ptFlipY
            simpa using show isHole m w (x, y) from ⟨by omega, hxn, by omega, hyn, hcov⟩
          have hle := (claim3a_corner_square_00 hm
            (isValidPerm_permReverse (isValidPerm_permComplement hw))
            (by omega) (by omega) (by omega) (by omega)).mp hhole_rc
          refine ⟨((N_odd m : ℤ), (N_odd m : ℤ)),
            by simpa using torusCenters_add_torus (zero_mem_torusCenters m w) 1 1, ?_⟩
          change taxicabDist ((N_odd m : ℤ), (N_odd m : ℤ)) (x, y) ≤ (m : ℤ)
          unfold taxicabDist; dsimp only
          rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
          omega

private def modN (m : ℕ) (z : ℤ × ℤ) : Fin (N_odd m) × Fin (N_odd m) :=
  (⟨(z.1 % (N_odd m : ℤ)).toNat, by
    have hN : (0 : ℤ) < (N_odd m : ℤ) := by exact_mod_cast N_odd_pos m
    have h1 := Int.emod_nonneg z.1 hN.ne'
    have h2 := Int.emod_lt_of_pos z.1 hN
    omega⟩,
   ⟨(z.2 % (N_odd m : ℤ)).toNat, by
    have hN : (0 : ℤ) < (N_odd m : ℤ) := by exact_mod_cast N_odd_pos m
    have h1 := Int.emod_nonneg z.2 hN.ne'
    have h2 := Int.emod_lt_of_pos z.2 hN
    omega⟩)

private theorem modN_add_torus (m : ℕ) (z : ℤ × ℤ) (a b : ℤ) :
    modN m (z.1 + a * (N_odd m : ℤ), z.2 + b * (N_odd m : ℤ)) = modN m z := by
  unfold modN
  ext <;> simp [Int.add_mul_emod_self_right]

private theorem modN_eq_iff (m : ℕ) (z₁ z₂ : ℤ × ℤ) :
    modN m z₁ = modN m z₂ ↔
      z₁.1 % (N_odd m : ℤ) = z₂.1 % (N_odd m : ℤ) ∧
      z₁.2 % (N_odd m : ℤ) = z₂.2 % (N_odd m : ℤ) := by
  have hN : (0 : ℤ) < (N_odd m : ℤ) := by exact_mod_cast N_odd_pos m
  have ha1 := Int.emod_nonneg z₁.1 hN.ne'
  have ha2 := Int.emod_nonneg z₂.1 hN.ne'
  have hb1 := Int.emod_nonneg z₁.2 hN.ne'
  have hb2 := Int.emod_nonneg z₂.2 hN.ne'
  unfold modN
  constructor
  · intro h
    have h1 := congrArg (fun p : Fin (N_odd m) × Fin (N_odd m) => (p.1.val : ℤ)) h
    have h2 := congrArg (fun p : Fin (N_odd m) × Fin (N_odd m) => (p.2.val : ℤ)) h
    dsimp only at h1 h2
    omega
  · intro ⟨h1, h2⟩
    ext <;> dsimp only <;> omega

/-- **Claim 6:** For any valid `w`, `torusCenters m w = (plot w ∪ {O}) + N ℤ^2` is a radius-`m`
Lee tiling of `ℤ^2` containing `O = (0, 0)`. -/
theorem claim6_torus_tiling {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) :
    IsLeeTiling m (torusCenters m w) ∧ (0, 0) ∈ torusCenters m w := by
  have hNpos : (0 : ℤ) < (N_odd m : ℤ) := by exact_mod_cast N_odd_pos m
  have hN1 : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  have hcov_all : ∀ z : ℤ × ℤ, ∃ c ∈ torusCenters m w, z ∈ leeSphere m c := by
    intro z
    let r₁ := z.1 % (N_odd m : ℤ)
    let q₁ := z.1 / (N_odd m : ℤ)
    let r₂ := z.2 % (N_odd m : ℤ)
    let q₂ := z.2 / (N_odd m : ℤ)
    have hr1 : 0 ≤ r₁ ∧ r₁ ≤ (n_odd m : ℤ) := by
      have := Int.emod_nonneg z.1 hNpos.ne'
      have := Int.emod_lt_of_pos z.1 hNpos
      omega
    have hr2 : 0 ≤ r₂ ∧ r₂ ≤ (n_odd m : ℤ) := by
      have := Int.emod_nonneg z.2 hNpos.ne'
      have := Int.emod_lt_of_pos z.2 hNpos
      omega
    obtain ⟨c, hc, hsph⟩ := torusCenters_cover_fundamental hm hw hr1.1 hr1.2 hr2.1 hr2.2
    refine ⟨(c.1 + q₁ * (N_odd m : ℤ), c.2 + q₂ * (N_odd m : ℤ)),
      torusCenters_add_torus hc q₁ q₂, ?_⟩
    change taxicabDist (c.1 + q₁ * (N_odd m : ℤ), c.2 + q₂ * (N_odd m : ℤ)) z ≤ (m : ℤ)
    have hz1 : z.1 = r₁ + q₁ * (N_odd m : ℤ) := by
      have := Int.emod_add_mul_ediv z.1 (N_odd m : ℤ); linarith
    have hz2 : z.2 = r₂ + q₂ * (N_odd m : ℤ) := by
      have := Int.emod_add_mul_ediv z.2 (N_odd m : ℤ); linarith
    have heq : z = (r₁ + q₁ * (N_odd m : ℤ), r₂ + q₂ * (N_odd m : ℤ)) := Prod.ext hz1 hz2
    rw [heq]
    unfold taxicabDist
    dsimp only
    have hs1 : (c.1 + q₁ * (N_odd m : ℤ)) - (r₁ + q₁ * (N_odd m : ℤ)) = c.1 - r₁ := by ring
    have hs2 : (c.2 + q₂ * (N_odd m : ℤ)) - (r₂ + q₂ * (N_odd m : ℤ)) = c.2 - r₂ := by ring
    rw [hs1, hs2]
    exact hsph
  let Qfin : Finset (ℤ × ℤ) := insert (0, 0) (plotFinset w)
  have hQmem : ∀ q : ℤ × ℤ, q ∈ Qfin ↔ q ∈ insert (0, 0) (plotSet w) := by
    intro q
    simp only [Qfin, Finset.mem_insert, plotFinset, Finset.mem_image, Finset.mem_univ, true_and,
      Set.mem_insert_iff, plotSet, Set.mem_range]
  have hQnot : (0, 0) ∉ plotFinset w := by
    simp only [plotFinset, Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨i, hi⟩
    have := plotPoint_mem_box w i
    rw [hi] at this
    omega
  have hQcard : Qfin.card = N_odd m := by
    rw [Finset.card_insert_of_notMem hQnot, plotFinset,
      Finset.card_image_of_injective _ (plotPoint_injective w), Finset.card_univ, Fintype.card_fin]
    exact n_odd_add_one m
  have huniv_sub : (Finset.univ : Finset (Fin (N_odd m) × Fin (N_odd m))) ⊆
      Qfin.biUnion (fun q => (leeSphereFinset m q).image (modN m)) := by
    intro u _
    obtain ⟨c, hc, hsph⟩ := torusCenters_cover_fundamental hm hw (x := (u.1.val : ℤ))
      (y := (u.2.val : ℤ)) (by omega) (by have := u.1.isLt; omega) (by omega)
      (by have := u.2.isLt; omega)
    obtain ⟨q, hq, a, b, rfl⟩ := hc
    rw [Finset.mem_biUnion]
    refine ⟨q, (hQmem q).mpr hq, Finset.mem_image.mpr ?_⟩
    refine ⟨((u.1.val : ℤ) - a * (N_odd m : ℤ), (u.2.val : ℤ) - b * (N_odd m : ℤ)), ?_, ?_⟩
    · rw [mem_leeSphereFinset]
      change taxicabDist q ((u.1.val : ℤ) - a * (N_odd m : ℤ), (u.2.val : ℤ) - b * (N_odd m : ℤ)) ≤ (m : ℤ)
      change taxicabDist (q.1 + a * (N_odd m : ℤ), q.2 + b * (N_odd m : ℤ))
        ((u.1.val : ℤ), (u.2.val : ℤ)) ≤ (m : ℤ) at hsph
      unfold taxicabDist at hsph ⊢
      dsimp only at hsph ⊢
      have heq1 : q.1 - ((u.1.val : ℤ) - a * (N_odd m : ℤ)) = (q.1 + a * (N_odd m : ℤ)) - (u.1.val : ℤ) := by ring
      have heq2 : q.2 - ((u.2.val : ℤ) - b * (N_odd m : ℤ)) = (q.2 + b * (N_odd m : ℤ)) - (u.2.val : ℤ) := by ring
      rw [heq1, heq2]
      exact hsph
    · have hm1 : ((u.1.val : ℤ) - a * (N_odd m : ℤ)) % (N_odd m : ℤ) = (u.1.val : ℤ) := by
        rw [sub_eq_add_neg, ← neg_mul, Int.add_mul_emod_self_right,
          Int.emod_eq_of_lt (by omega) (by exact_mod_cast u.1.isLt)]
      have hm2 : ((u.2.val : ℤ) - b * (N_odd m : ℤ)) % (N_odd m : ℤ) = (u.2.val : ℤ) := by
        rw [sub_eq_add_neg, ← neg_mul, Int.add_mul_emod_self_right,
          Int.emod_eq_of_lt (by omega) (by exact_mod_cast u.2.isLt)]
      unfold modN
      ext <;> dsimp only
      · rw [hm1]; simp
      · rw [hm2]; simp
  have hcard_chain :
      N_odd m ^ 2 ≤ (Qfin.biUnion (fun q => (leeSphereFinset m q).image (modN m))).card ∧
      (Qfin.biUnion (fun q => (leeSphereFinset m q).image (modN m))).card ≤
        ∑ q ∈ Qfin, ((leeSphereFinset m q).image (modN m)).card ∧
      ∑ q ∈ Qfin, ((leeSphereFinset m q).image (modN m)).card ≤
        ∑ q ∈ Qfin, (leeSphereFinset m q).card ∧
      ∑ q ∈ Qfin, (leeSphereFinset m q).card = N_odd m ^ 2 := by
    refine ⟨?_, Finset.card_biUnion_le, Finset.sum_le_sum fun q _ => Finset.card_image_le, ?_⟩
    · have h := Finset.card_le_card huniv_sub
      simpa [Fintype.card_prod, Fintype.card_fin, sq] using h
    · have hcongr : ∑ q ∈ Qfin, (leeSphereFinset m q).card = ∑ _q ∈ Qfin, N_odd m :=
        Finset.sum_congr rfl fun q _ => card_leeSphereFinset m q
      rw [hcongr, Finset.sum_const, hQcard, smul_eq_mul, sq]
  have hbi_eq : (Qfin.biUnion (fun q => (leeSphereFinset m q).image (modN m))).card =
      ∑ q ∈ Qfin, ((leeSphereFinset m q).image (modN m)).card := by omega
  have him_sum_eq : ∑ q ∈ Qfin, ((leeSphereFinset m q).image (modN m)).card =
      ∑ q ∈ Qfin, (leeSphereFinset m q).card := by omega
  have hpd_Q : (Qfin : Set (ℤ × ℤ)).PairwiseDisjoint
      (fun q => (leeSphereFinset m q).image (modN m)) := by
    -- Pairwise disjointness from card_biUnion = sum
    have haux : ∀ S : Finset (ℤ × ℤ),
        (S.biUnion (fun q => (leeSphereFinset m q).image (modN m))).card =
          ∑ q ∈ S, ((leeSphereFinset m q).image (modN m)).card →
        (S : Set (ℤ × ℤ)).PairwiseDisjoint
          (fun q => (leeSphereFinset m q).image (modN m)) := by
      intro S hS
      induction S using Finset.induction with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.biUnion_insert, Finset.sum_insert ha] at hS
        have hc := Finset.card_union_add_card_inter
          ((leeSphereFinset m a).image (modN m))
          (s.biUnion (fun q => (leeSphereFinset m q).image (modN m)))
        have hle : (s.biUnion (fun q => (leeSphereFinset m q).image (modN m))).card ≤
            ∑ q ∈ s, ((leeSphereFinset m q).image (modN m)).card := Finset.card_biUnion_le
        have hi0 : (((leeSphereFinset m a).image (modN m)) ∩
            (s.biUnion (fun q => (leeSphereFinset m q).image (modN m)))).card = 0 := by omega
        have hdisj_a : Disjoint ((leeSphereFinset m a).image (modN m))
            (s.biUnion (fun q => (leeSphereFinset m q).image (modN m))) :=
          Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hi0)
        have hsub_pd := ih (by omega)
        intro x hx y hy hxy
        rw [Finset.mem_coe, Finset.mem_insert] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact Finset.disjoint_of_subset_right
            (Finset.subset_biUnion_of_mem (fun q => (leeSphereFinset m q).image (modN m)) hy) hdisj_a
        · exact (Finset.disjoint_of_subset_right
            (Finset.subset_biUnion_of_mem (fun q => (leeSphereFinset m q).image (modN m)) hx) hdisj_a).symm
        · exact hsub_pd hx hy hxy
    exact haux Qfin hbi_eq
  have hinj_on_sphere : ∀ q ∈ Qfin, Set.InjOn (modN m) (leeSphereFinset m q : Set (ℤ × ℤ)) := by
    intro q hq
    have hcard_q : ((leeSphereFinset m q).image (modN m)).card = (leeSphereFinset m q).card := by
      by_contra hne
      have hlt : ((leeSphereFinset m q).image (modN m)).card < (leeSphereFinset m q).card :=
        lt_of_le_of_ne Finset.card_image_le hne
      have hsum_lt := Finset.sum_lt_sum (fun q' _ => Finset.card_image_le (f := modN m) (s := leeSphereFinset m q')) ⟨q, hq, hlt⟩
      omega
    exact Finset.card_image_iff.mp hcard_q
  refine ⟨⟨?_, hcov_all⟩, zero_mem_torusCenters m w⟩
  rintro c₁ ⟨q₁, hq1, a₁, b₁, rfl⟩ c₂ ⟨q₂, hq2, a₂, b₂, rfl⟩ hne
  rw [Set.disjoint_left]
  intro z hz1 hz2
  apply hne
  let z₁ : ℤ × ℤ := (z.1 - a₁ * (N_odd m : ℤ), z.2 - b₁ * (N_odd m : ℤ))
  let z₂ : ℤ × ℤ := (z.1 - a₂ * (N_odd m : ℤ), z.2 - b₂ * (N_odd m : ℤ))
  have hz1_sph : z₁ ∈ leeSphereFinset m q₁ := by
    rw [mem_leeSphereFinset]
    change taxicabDist q₁ z₁ ≤ (m : ℤ)
    change taxicabDist (q₁.1 + a₁ * (N_odd m : ℤ), q₁.2 + b₁ * (N_odd m : ℤ)) z ≤ (m : ℤ) at hz1
    unfold taxicabDist at hz1 ⊢
    dsimp only [z₁] at hz1 ⊢
    have e1 : q₁.1 - (z.1 - a₁ * (N_odd m : ℤ)) = (q₁.1 + a₁ * (N_odd m : ℤ)) - z.1 := by ring
    have e2 : q₁.2 - (z.2 - b₁ * (N_odd m : ℤ)) = (q₁.2 + b₁ * (N_odd m : ℤ)) - z.2 := by ring
    rw [e1, e2]; exact hz1
  have hz2_sph : z₂ ∈ leeSphereFinset m q₂ := by
    rw [mem_leeSphereFinset]
    change taxicabDist q₂ z₂ ≤ (m : ℤ)
    change taxicabDist (q₂.1 + a₂ * (N_odd m : ℤ), q₂.2 + b₂ * (N_odd m : ℤ)) z ≤ (m : ℤ) at hz2
    unfold taxicabDist at hz2 ⊢
    dsimp only [z₂] at hz2 ⊢
    have e1 : q₂.1 - (z.1 - a₂ * (N_odd m : ℤ)) = (q₂.1 + a₂ * (N_odd m : ℤ)) - z.1 := by ring
    have e2 : q₂.2 - (z.2 - b₂ * (N_odd m : ℤ)) = (q₂.2 + b₂ * (N_odd m : ℤ)) - z.2 := by ring
    rw [e1, e2]; exact hz2
  have hmod1 : modN m z₁ = modN m z := by
    have hz_eq : z = (z₁.1 + a₁ * (N_odd m : ℤ), z₁.2 + b₁ * (N_odd m : ℤ)) := by
      ext <;> dsimp [z₁] <;> ring
    conv_rhs => rw [hz_eq]
    exact (modN_add_torus m z₁ a₁ b₁).symm
  have hmod2 : modN m z₂ = modN m z := by
    have hz_eq : z = (z₂.1 + a₂ * (N_odd m : ℤ), z₂.2 + b₂ * (N_odd m : ℤ)) := by
      ext <;> dsimp [z₂] <;> ring
    conv_rhs => rw [hz_eq]
    exact (modN_add_torus m z₂ a₂ b₂).symm
  have hq_eq : q₁ = q₂ := by
    by_contra hqne
    have hdisj := hpd_Q ((hQmem q₁).mpr hq1) ((hQmem q₂).mpr hq2) hqne
    exact Finset.disjoint_left.mp hdisj
      (Finset.mem_image.mpr ⟨z₁, hz1_sph, hmod1⟩)
      (Finset.mem_image.mpr ⟨z₂, hz2_sph, hmod2⟩)
  subst hq_eq
  have hz_eq := hinj_on_sphere q₁ ((hQmem q₁).mpr hq1) hz1_sph hz2_sph (hmod1.trans hmod2.symm)
  have hfst := congrArg Prod.fst hz_eq
  have hsnd := congrArg Prod.snd hz_eq
  dsimp [z₁, z₂] at hfst hsnd
  have ha : a₁ = a₂ := by nlinarith
  have hb : b₁ = b₂ := by nlinarith
  subst ha; subst hb; rfl

/-! ## Section 2: Lattices `Λ⁺`, `Λ⁻` and Their Tiling Properties (Steps 7–8) -/

/-- Basis vector `e₁ = (m + 1, m)`. -/
def e1 (m : ℕ) : ℤ × ℤ := ((m : ℤ) + 1, (m : ℤ))

/-- Basis vector `e₂ = (-m, m + 1)`. -/
def e2 (m : ℕ) : ℤ × ℤ := (-(m : ℤ), (m : ℤ) + 1)

/-- Lattice `Λ⁺ = ℤ e₁ + ℤ e₂`. -/
def LambdaPlus (m : ℕ) : Set (ℤ × ℤ) :=
  { z | ∃ i j : ℤ, z = (i * ((m : ℤ) + 1) - j * (m : ℤ), i * (m : ℤ) + j * ((m : ℤ) + 1)) }

/-- Mirror lattice `Λ⁻` under `(x, y) ↦ (-x, y)`. -/
def LambdaMinus (m : ℕ) : Set (ℤ × ℤ) :=
  { z | ∃ i j : ℤ, z = (-(i * ((m : ℤ) + 1) - j * (m : ℤ)), i * (m : ℤ) + j * ((m : ℤ) + 1)) }

/-- **(Step 8)** Algebraic characterization `Λ⁺ = {(x, y) | N ∣ (y - d * x)}`. -/
theorem mem_LambdaPlus_iff_dvd (m : ℕ) (z : ℤ × ℤ) :
    z ∈ LambdaPlus m ↔ (N_odd m : ℤ) ∣ (z.2 - (d_odd m : ℤ) * z.1) := by
  have hN : (N_odd m : ℤ) = 2 * (m : ℤ) ^ 2 + 2 * (m : ℤ) + 1 := by unfold N_odd; push_cast; ring
  have hd : (d_odd m : ℤ) = 2 * (m : ℤ) + 1 := by unfold d_odd; push_cast; ring
  constructor
  · rintro ⟨i, j, rfl⟩
    refine ⟨j - i, ?_⟩
    rw [hN, hd]; dsimp only; ring
  · rintro ⟨k, hk⟩
    refine ⟨z.1 + k * (m : ℤ), z.1 + k * ((m : ℤ) + 1), ?_⟩
    have hy : z.2 = (d_odd m : ℤ) * z.1 + k * (N_odd m : ℤ) := by linarith
    ext <;> dsimp only
    · ring
    · rw [hy, hN, hd]; ring

/-- **(Step 8)** Algebraic characterization `Λ⁻ = {(x, y) | N ∣ (y + d * x)}`. -/
theorem mem_LambdaMinus_iff_dvd (m : ℕ) (z : ℤ × ℤ) :
    z ∈ LambdaMinus m ↔ (N_odd m : ℤ) ∣ (z.2 + (d_odd m : ℤ) * z.1) := by
  have hm_iff : z ∈ LambdaMinus m ↔ (-z.1, z.2) ∈ LambdaPlus m := by
    unfold LambdaMinus LambdaPlus
    constructor
    · rintro ⟨i, j, h⟩
      refine ⟨i, j, ?_⟩
      ext
      · have := congrArg Prod.fst h; dsimp only at this ⊢; linarith
      · have := congrArg Prod.snd h; dsimp only at this ⊢; exact this
    · rintro ⟨i, j, h⟩
      refine ⟨i, j, ?_⟩
      ext
      · have := congrArg Prod.fst h; dsimp only at this ⊢; linarith
      · have := congrArg Prod.snd h; dsimp only at this ⊢; exact this
  rw [hm_iff, mem_LambdaPlus_iff_dvd]
  dsimp only
  ring_nf

private theorem lambdaPlus_nonzero_norm {m : ℕ} (hm : 1 ≤ m) {z : ℤ × ℤ}
    (hz : z ∈ LambdaPlus m) (hne : z ≠ (0, 0)) :
    2 * (m : ℤ) + 1 ≤ taxicabNorm z := by
  obtain ⟨i, j, rfl⟩ := hz
  have hij : i ≠ 0 ∨ j ≠ 0 := by
    by_contra h0
    push Not at h0
    rcases h0 with ⟨rfl, rfl⟩
    apply hne
    simp
  let x := i * ((m : ℤ) + 1) - j * (m : ℤ)
  let y := i * (m : ℤ) + j * ((m : ℤ) + 1)
  change 2 * (m : ℤ) + 1 ≤ |x| + |y|
  have hsum : x + y = i * (2 * (m : ℤ) + 1) + j := by dsimp [x, y]; ring
  have hdiff : x - y = i - j * (2 * (m : ℤ) + 1) := by dsimp [x, y]; ring
  have hab_sum : |x + y| ≤ |x| + |y| := abs_add_le x y
  have hab_diff : |x - y| ≤ |x| + |y| := (abs_sub_le x 0 y).trans_eq (by simp)
  rcases le_or_gt |j| |i| with hji | hij_lt
  · have hi0 : i ≠ 0 := by
      rcases hij with hi | hj
      · exact hi
      · intro hi0; rw [hi0, abs_zero] at hji; have := abs_nonneg j; exact hj (abs_eq_zero.mp (by omega))
    have hi_abs : 1 ≤ |i| := by
      rcases le_or_gt 0 i with h | h <;> [rw [abs_of_nonneg h]; rw [abs_of_neg h]] <;> omega
    by_cases hi1 : |i| = 1
    · have hj_le : |j| ≤ 1 := by omega
      have hj_cases : j = -1 ∨ j = 0 ∨ j = 1 := by
        rcases le_or_gt 0 j with h | h <;> [rw [abs_of_nonneg h] at hj_le; rw [abs_of_neg h] at hj_le] <;> omega
      have hi_cases : i = 1 ∨ i = -1 := by
        rcases le_or_gt 0 i with h | h <;> [rw [abs_of_nonneg h] at hi1; rw [abs_of_neg h] at hi1] <;> omega
      rcases hi_cases with rfl | rfl <;> rcases hj_cases with rfl | rfl | rfl
      · -- (1, -1): x = 2m+1, y = -1
        dsimp [x, y]; rw [abs_of_nonneg (by omega), abs_of_neg (by omega)]; omega
      · -- (1, 0): x = m+1, y = m
        dsimp [x, y]; rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega
      · -- (1, 1): x = 1, y = 2m+1
        dsimp [x, y]; rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega
      · -- (-1, -1): x = -1, y = -(2m+1)
        dsimp [x, y]; rw [abs_of_neg (by omega), abs_of_neg (by omega)]; omega
      · -- (-1, 0): x = -(m+1), y = -m
        dsimp [x, y]; rw [abs_of_neg (by omega), abs_of_neg (by omega)]; omega
      · -- (-1, 1): x = -(2m+1), y = 1
        dsimp [x, y]; rw [abs_of_neg (by omega), abs_of_nonneg (by omega)]; omega
    · have hi2 : 2 ≤ |i| := by omega
      have htri : (2 * (m : ℤ) + 1) * |i| - |j| ≤ |i * (2 * (m : ℤ) + 1) + j| := by
        have h1 := abs_sub_abs_le_abs_sub (i * (2 * (m : ℤ) + 1)) (-j)
        rw [sub_neg_eq_add, abs_neg, abs_mul, abs_of_pos (by omega : 0 < 2 * (m : ℤ) + 1)] at h1
        linarith
      have hge : 2 * (m : ℤ) + 1 ≤ (2 * (m : ℤ) + 1) * |i| - |j| := by nlinarith
      linarith [hsum ▸ hab_sum]
  · have hj0 : j ≠ 0 := by
      intro hj0; rw [hj0, abs_zero] at hij_lt; have := abs_nonneg i; omega
    have hj_abs : 1 ≤ |j| := by
      rcases le_or_gt 0 j with h | h <;> [rw [abs_of_nonneg h]; rw [abs_of_neg h]] <;> omega
    by_cases hj1 : |j| = 1
    · have hi0 : i = 0 := by
        rcases le_or_gt 0 i with h | h <;> [rw [abs_of_nonneg h] at hij_lt; rw [abs_of_neg h] at hij_lt] <;> omega
      subst hi0
      have hj_cases : j = 1 ∨ j = -1 := by
        rcases le_or_gt 0 j with h | h <;> [rw [abs_of_nonneg h] at hj1; rw [abs_of_neg h] at hj1] <;> omega
      rcases hj_cases with rfl | rfl
      · dsimp [x, y]; rw [abs_of_neg (by omega), abs_of_nonneg (by omega)]; omega
      · dsimp [x, y]; rw [abs_of_nonneg (by omega), abs_of_neg (by omega)]; omega
    · have hj2 : 2 ≤ |j| := by omega
      have htri : (2 * (m : ℤ) + 1) * |j| - |i| ≤ |i - j * (2 * (m : ℤ) + 1)| := by
        have h1 := abs_sub_abs_le_abs_sub (j * (2 * (m : ℤ) + 1)) i
        rw [abs_sub_comm (j * (2 * (m : ℤ) + 1)) i, abs_mul,
          abs_of_pos (by omega : 0 < 2 * (m : ℤ) + 1)] at h1
        linarith
      have hge : 2 * (m : ℤ) + 1 ≤ (2 * (m : ℤ) + 1) * |j| - |i| := by nlinarith
      linarith [hdiff ▸ hab_diff]

theorem LambdaPlus_dist {m : ℕ} (hm : 1 ≤ m) {p q : ℤ × ℤ}
    (hp : p ∈ LambdaPlus m) (hq : q ∈ LambdaPlus m) (hpq : p ≠ q) :
    2 * (m : ℤ) + 1 ≤ taxicabDist p q := by
  have hsub : (p.1 - q.1, p.2 - q.2) ∈ LambdaPlus m := by
    rw [mem_LambdaPlus_iff_dvd] at hp hq ⊢
    dsimp only
    have heq : (p.2 - q.2) - (d_odd m : ℤ) * (p.1 - q.1) =
        (p.2 - (d_odd m : ℤ) * p.1) - (q.2 - (d_odd m : ℤ) * q.1) := by ring
    rw [heq]
    exact dvd_sub hp hq
  have hne : (p.1 - q.1, p.2 - q.2) ≠ (0, 0) := by
    intro h; apply hpq
    exact Prod.ext (sub_eq_zero.mp (Prod.mk.inj h).1) (sub_eq_zero.mp (Prod.mk.inj h).2)
  exact lambdaPlus_nonzero_norm hm hsub hne

theorem LambdaPlus_isLeeTiling {m : ℕ} (hm : 1 ≤ m) : IsLeeTiling m (LambdaPlus m) := by
  have hNpos : (0 : ℤ) < (N_odd m : ℤ) := by exact_mod_cast N_odd_pos m
  constructor
  · intro c hc c' hc' hne
    rw [sphere_disjoint_iff]
    exact LambdaPlus_dist hm hc hc' hne
  · intro z
    let res : ℤ × ℤ → Fin (N_odd m) := fun q =>
      ⟨((q.2 - (d_odd m : ℤ) * q.1) % (N_odd m : ℤ)).toNat, by
        have h1 := Int.emod_nonneg (q.2 - (d_odd m : ℤ) * q.1) hNpos.ne'
        have h2 := Int.emod_lt_of_pos (q.2 - (d_odd m : ℤ) * q.1) hNpos
        omega⟩
    have hinj : Set.InjOn res (leeSphereFinset m (0, 0) : Set (ℤ × ℤ)) := by
      intro q₁ hq1 q₂ hq2 hres
      by_contra hne
      have hdvd : (N_odd m : ℤ) ∣ ((q₁.2 - q₂.2) - (d_odd m : ℤ) * (q₁.1 - q₂.1)) := by
        have hmod : (q₁.2 - (d_odd m : ℤ) * q₁.1) % (N_odd m : ℤ) =
            (q₂.2 - (d_odd m : ℤ) * q₂.1) % (N_odd m : ℤ) := by
          have hv := congrArg Fin.val hres
          dsimp [res] at hv
          have h1 := Int.emod_nonneg (q₁.2 - (d_odd m : ℤ) * q₁.1) hNpos.ne'
          have h2 := Int.emod_nonneg (q₂.2 - (d_odd m : ℤ) * q₂.1) hNpos.ne'
          omega
        have hd := Int.ModEq.dvd (show (q₂.2 - (d_odd m : ℤ) * q₂.1) ≡
            (q₁.2 - (d_odd m : ℤ) * q₁.1) [ZMOD (N_odd m : ℤ)] from hmod.symm)
        have heq : (q₁.2 - (d_odd m : ℤ) * q₁.1) - (q₂.2 - (d_odd m : ℤ) * q₂.1) =
            (q₁.2 - q₂.2) - (d_odd m : ℤ) * (q₁.1 - q₂.1) := by ring
        rwa [← heq]
      have hmem : (q₁.1 - q₂.1, q₁.2 - q₂.2) ∈ LambdaPlus m :=
        (mem_LambdaPlus_iff_dvd m _).mpr hdvd
      have hnz : (q₁.1 - q₂.1, q₁.2 - q₂.2) ≠ (0, 0) := by
        intro h; apply hne
        exact Prod.ext (sub_eq_zero.mp (Prod.mk.inj h).1) (sub_eq_zero.mp (Prod.mk.inj h).2)
      have hge := lambdaPlus_nonzero_norm hm hmem hnz
      rw [Finset.mem_coe, mem_leeSphereFinset] at hq1 hq2
      change taxicabDist (0, 0) q₁ ≤ (m : ℤ) at hq1
      change taxicabDist (0, 0) q₂ ≤ (m : ℤ) at hq2
      have htri := taxicabDist_triangle q₁ (0, 0) q₂
      rw [taxicabDist_comm q₁ (0, 0)] at htri
      have htri2 : taxicabDist q₁ q₂ ≤ 2 * (m : ℤ) := by linarith
      change 2 * (m : ℤ) + 1 ≤ taxicabDist q₁ q₂ at hge
      omega
    have him_eq : ((leeSphereFinset m (0, 0)).image res) = Finset.univ := by
      refine Finset.eq_univ_of_card _ ?_
      rw [Finset.card_image_of_injOn hinj, card_leeSphereFinset, Fintype.card_fin]
      rfl
    have hmem_univ : res z ∈ (leeSphereFinset m (0, 0)).image res := by
      rw [him_eq]; exact Finset.mem_univ _
    obtain ⟨q, hq, hres_q⟩ := Finset.mem_image.mp hmem_univ
    rw [mem_leeSphereFinset] at hq
    change taxicabDist (0, 0) q ≤ (m : ℤ) at hq
    let c : ℤ × ℤ := (z.1 - q.1, z.2 - q.2)
    have hc_mem : c ∈ LambdaPlus m := by
      rw [mem_LambdaPlus_iff_dvd]
      have hmod : (q.2 - (d_odd m : ℤ) * q.1) % (N_odd m : ℤ) =
          (z.2 - (d_odd m : ℤ) * z.1) % (N_odd m : ℤ) := by
        have hv := congrArg Fin.val hres_q
        dsimp [res] at hv
        have h1 := Int.emod_nonneg (q.2 - (d_odd m : ℤ) * q.1) hNpos.ne'
        have h2 := Int.emod_nonneg (z.2 - (d_odd m : ℤ) * z.1) hNpos.ne'
        omega
      have hd := Int.ModEq.dvd (show (q.2 - (d_odd m : ℤ) * q.1) ≡
          (z.2 - (d_odd m : ℤ) * z.1) [ZMOD (N_odd m : ℤ)] from hmod)
      have heq : (z.2 - (d_odd m : ℤ) * z.1) - (q.2 - (d_odd m : ℤ) * q.1) =
          (z.2 - q.2) - (d_odd m : ℤ) * (z.1 - q.1) := by ring
      dsimp [c]; rwa [← heq]
    refine ⟨c, hc_mem, ?_⟩
    change taxicabDist c z ≤ (m : ℤ)
    have hdist : taxicabDist c z = taxicabDist (0, 0) q := by
      unfold taxicabDist c; dsimp only; ring_nf
    rw [hdist]
    exact hq

/-! ## Section 3: Step 7 — Every Radius-`m` Lee Tiling Containing `O` is `Λ⁺` or `Λ⁻` -/

private theorem isLeeTiling_translate {m : ℕ} {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T)
    (c₀ : ℤ × ℤ) :
    IsLeeTiling m { p | (p.1 + c₀.1, p.2 + c₀.2) ∈ T } := by
  constructor
  · intro c hc c' hc' hne
    have hd := hT.1 _ hc _ hc' (fun h => hne (Prod.ext (by have := (Prod.mk.inj h).1; omega)
      (by have := (Prod.mk.inj h).2; omega)))
    rw [sphere_disjoint_iff] at hd ⊢
    rwa [← taxicabDist_translate c c' c₀]
  · intro z
    obtain ⟨c, hc, hsph⟩ := hT.2 (z.1 + c₀.1, z.2 + c₀.2)
    refine ⟨(c.1 - c₀.1, c.2 - c₀.2), ?_, ?_⟩
    · change ((c.1 - c₀.1) + c₀.1, (c.2 - c₀.2) + c₀.2) ∈ T
      simpa using hc
    · change taxicabDist (c.1 - c₀.1, c.2 - c₀.2) z ≤ (m : ℤ)
      change taxicabDist c (z.1 + c₀.1, z.2 + c₀.2) ≤ (m : ℤ) at hsph
      unfold taxicabDist at hsph ⊢; dsimp only at hsph ⊢
      have e1 : c.1 - c₀.1 - z.1 = c.1 - (z.1 + c₀.1) := by ring
      have e2 : c.2 - c₀.2 - z.2 = c.2 - (z.2 + c₀.2) := by ring
      rw [e1, e2]; exact hsph

private theorem isLeeTiling_rhoInv {m : ℕ} {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T) :
    IsLeeTiling m { p | (-p.2, p.1) ∈ T } := by
  constructor
  · intro c hc c' hc' hne
    have hd := hT.1 _ hc _ hc' (fun h => hne (Prod.ext (Prod.mk.inj h).2
      (by have := (Prod.mk.inj h).1; omega)))
    rw [sphere_disjoint_iff] at hd ⊢
    have heq : taxicabDist (-c.2, c.1) (-c'.2, c'.1) = taxicabDist c c' := by
      unfold taxicabDist; dsimp only
      have h1 : |-c.2 - -c'.2| = |c.2 - c'.2| := by rw [← abs_neg]; ring_nf
      rw [h1, add_comm]
    rwa [heq] at hd
  · intro z
    obtain ⟨c, hc, hsph⟩ := hT.2 (-z.2, z.1)
    refine ⟨(c.2, -c.1), ?_, ?_⟩
    · simpa using hc
    · change taxicabDist (c.2, -c.1) z ≤ (m : ℤ)
      change taxicabDist c (-z.2, z.1) ≤ (m : ℤ) at hsph
      unfold taxicabDist at hsph ⊢; dsimp only at hsph ⊢
      have h1 : |-c.1 - z.2| = |c.1 - -z.2| := by rw [← abs_neg]; ring_nf
      rw [h1, add_comm]
      exact hsph

private theorem isLeeTiling_mirrorX {m : ℕ} {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T) :
    IsLeeTiling m { p | (-p.1, p.2) ∈ T } := by
  constructor
  · intro c hc c' hc' hne
    have hd := hT.1 _ hc _ hc' (fun h => hne (Prod.ext (by have := (Prod.mk.inj h).1; omega)
      (Prod.mk.inj h).2))
    rw [sphere_disjoint_iff] at hd ⊢
    have heq : taxicabDist (-c.1, c.2) (-c'.1, c'.2) = taxicabDist c c' := by
      unfold taxicabDist; dsimp only
      have h1 : |-c.1 - -c'.1| = |c.1 - c'.1| := by rw [← abs_neg]; ring_nf
      rw [h1]
    rwa [heq] at hd
  · intro z
    obtain ⟨c, hc, hsph⟩ := hT.2 (-z.1, z.2)
    refine ⟨(-c.1, c.2), ?_, ?_⟩
    · simpa using hc
    · change taxicabDist (-c.1, c.2) z ≤ (m : ℤ)
      change taxicabDist c (-z.1, z.2) ≤ (m : ℤ) at hsph
      unfold taxicabDist at hsph ⊢; dsimp only at hsph ⊢
      have h1 : |-c.1 - z.1| = |c.1 - -z.1| := by rw [← abs_neg]; ring_nf
      rw [h1]
      exact hsph

/-- **Step 7(i) The rule at the origin:** If `T` is a Lee tiling with `O ∈ T` and `e₂ ∈ T`,
then `e₁ ∈ T`. -/
private theorem tiling_rule_origin {m : ℕ} (hm : 1 ≤ m) {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T)
    (hO : (0, 0) ∈ T) (he2 : e2 m ∈ T) :
    e1 m ∈ T := by
  let z : ℤ × ℤ := (1, (m : ℤ))
  obtain ⟨c'', hc'', hsph⟩ := hT.2 z
  have hneO : c'' ≠ (0, 0) := by
    rintro rfl
    change taxicabDist (0, 0) z ≤ (m : ℤ) at hsph
    unfold taxicabDist z at hsph; dsimp only at hsph
    rw [abs_of_neg (by omega), abs_of_nonpos (by omega)] at hsph
    omega
  have hnee2 : c'' ≠ e2 m := by
    rintro rfl
    change taxicabDist (e2 m) z ≤ (m : ℤ) at hsph
    unfold taxicabDist e2 z at hsph; dsimp only at hsph
    rw [abs_of_neg (by omega), abs_of_pos (by omega)] at hsph
    omega
  have hdO := (sphere_disjoint_iff m c'' (0, 0)).mp (hT.1 c'' hc'' (0, 0) hO hneO)
  have hde2 := (sphere_disjoint_iff m c'' (e2 m)).mp (hT.1 c'' hc'' (e2 m) he2 hnee2)
  change taxicabDist c'' z ≤ (m : ℤ) at hsph
  let a := c''.1 - 1
  let b := c''.2 - (m : ℤ)
  have hc_eq : c'' = (1 + a, (m : ℤ) + b) := by ext <;> dsimp [a, b] <;> ring
  rw [hc_eq] at hsph hdO hde2
  unfold taxicabDist at hsph hdO hde2
  dsimp only [z, e2] at hsph hdO hde2
  have hsp : |a| + |b| ≤ (m : ℤ) := by
    have : |(1 + a) - 1| = |a| := by ring_nf
    have : |((m : ℤ) + b) - (m : ℤ)| = |b| := by ring_nf
    linarith
  have hd1 : 2 * (m : ℤ) + 1 ≤ |1 + a| + |(m : ℤ) + b| := by simpa using hdO
  have hd2 : 2 * (m : ℤ) + 1 ≤ |1 + a + (m : ℤ)| + |b - 1| := by
    have e1 : (1 + a) - -(m : ℤ) = 1 + a + (m : ℤ) := by ring
    have e2 : ((m : ℤ) + b) - ((m : ℤ) + 1) = b - 1 := by ring
    rwa [e1, e2] at hde2
  have hab_m : a = (m : ℤ) ∧ b = 0 := by
    rcases le_or_gt 0 a with ha0 | ha0 <;>
    rcases le_or_gt 0 b with hb0 | hb0 <;>
    rcases le_or_gt 0 (1 + a) with h1a | h1a <;>
    rcases le_or_gt 0 ((m : ℤ) + b) with hmb | hmb <;>
    rcases le_or_gt 0 (1 + a + (m : ℤ)) with h1am | h1am <;>
    rcases le_or_gt 0 (b - 1) with hb1 | hb1 <;>
    (simp only [abs_of_nonneg, abs_of_neg, *] at hsp hd1 hd2; omega)
  have hce1 : c'' = e1 m := by rw [hc_eq, hab_m.1, hab_m.2]; ext <;> dsimp [e1] <;> ring
  rwa [← hce1]

private theorem tiling_rule {m : ℕ} (hm : 1 ≤ m) {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T)
    {c : ℤ × ℤ} (hc : c ∈ T) :
    ((c.1 + (e2 m).1, c.2 + (e2 m).2) ∈ T → (c.1 + (e1 m).1, c.2 + (e1 m).2) ∈ T) ∧
    ((c.1 - (e1 m).1, c.2 - (e1 m).2) ∈ T → (c.1 + (e2 m).1, c.2 + (e2 m).2) ∈ T) ∧
    ((c.1 - (e2 m).1, c.2 - (e2 m).2) ∈ T → (c.1 - (e1 m).1, c.2 - (e1 m).2) ∈ T) ∧
    ((c.1 + (e1 m).1, c.2 + (e1 m).2) ∈ T → (c.1 - (e2 m).1, c.2 - (e2 m).2) ∈ T) := by
  let T0 : Set (ℤ × ℤ) := { p | (p.1 + c.1, p.2 + c.2) ∈ T }
  have hT0 : IsLeeTiling m T0 := isLeeTiling_translate hT c
  have hO0 : (0, 0) ∈ T0 := by simpa [T0] using hc
  let T1 : Set (ℤ × ℤ) := { p | (-p.2, p.1) ∈ T0 }
  have hT1 : IsLeeTiling m T1 := isLeeTiling_rhoInv hT0
  have hO1 : (0, 0) ∈ T1 := by simpa [T1] using hO0
  let T2 : Set (ℤ × ℤ) := { p | (-p.2, p.1) ∈ T1 }
  have hT2 : IsLeeTiling m T2 := isLeeTiling_rhoInv hT1
  have hO2 : (0, 0) ∈ T2 := by simpa [T2] using hO1
  let T3 : Set (ℤ × ℤ) := { p | (-p.2, p.1) ∈ T2 }
  have hT3 : IsLeeTiling m T3 := isLeeTiling_rhoInv hT2
  have hO3 : (0, 0) ∈ T3 := by simpa [T3] using hO2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hmem : e2 m ∈ T0 := by
      change ((e2 m).1 + c.1, (e2 m).2 + c.2) ∈ T
      simpa [add_comm] using h
    have hout := tiling_rule_origin hm hT0 hO0 hmem
    change ((e1 m).1 + c.1, (e1 m).2 + c.2) ∈ T at hout
    simpa [add_comm] using hout
  · intro h
    have hmem : e2 m ∈ T1 := by
      show (-((m : ℤ) + 1) + c.1, -(m : ℤ) + c.2) ∈ T
      dsimp only [e1] at h
      have heq : (-((m : ℤ) + 1) + c.1, -(m : ℤ) + c.2) = (c.1 - ((m : ℤ) + 1), c.2 - (m : ℤ)) := by
        ext <;> ring
      rwa [heq]
    have hout := tiling_rule_origin hm hT1 hO1 hmem
    have hout' : (-(m : ℤ) + c.1, ((m : ℤ) + 1) + c.2) ∈ T := hout
    dsimp only [e2]
    have heq : (-(m : ℤ) + c.1, ((m : ℤ) + 1) + c.2) = (c.1 + -(m : ℤ), c.2 + ((m : ℤ) + 1)) := by
      ext <;> ring
    rwa [heq] at hout'
  · intro h
    have hmem : e2 m ∈ T2 := by
      show (-(e2 m).1 + c.1, -(e2 m).2 + c.2) ∈ T
      simpa [sub_eq_add_neg, add_comm] using h
    have hout := tiling_rule_origin hm hT2 hO2 hmem
    have hout' : (-(e1 m).1 + c.1, -(e1 m).2 + c.2) ∈ T := hout
    simpa [sub_eq_add_neg, add_comm] using hout'
  · intro h
    have hmem : e2 m ∈ T3 := by
      show (-(-((m : ℤ) + 1)) + c.1, -(-(m : ℤ)) + c.2) ∈ T
      dsimp only [e1] at h
      have heq : (-(-((m : ℤ) + 1)) + c.1, -(-(m : ℤ)) + c.2) = (c.1 + ((m : ℤ) + 1), c.2 + (m : ℤ)) := by
        ext <;> ring
      rwa [heq]
    have hout := tiling_rule_origin hm hT3 hO3 hmem
    have hout' : (-(-(m : ℤ)) + c.1, -((m : ℤ) + 1) + c.2) ∈ T := hout
    dsimp only [e2]
    have heq : (-(-(m : ℤ)) + c.1, -((m : ℤ) + 1) + c.2) = (c.1 - -(m : ℤ), c.2 - ((m : ℤ) + 1)) := by
      ext <;> ring
    rwa [heq] at hout'

private def IsFull (m : ℕ) (T : Set (ℤ × ℤ)) (c : ℤ × ℤ) : Prop :=
  c ∈ T ∧
  (c.1 + (e1 m).1, c.2 + (e1 m).2) ∈ T ∧
  (c.1 - (e1 m).1, c.2 - (e1 m).2) ∈ T ∧
  (c.1 + (e2 m).1, c.2 + (e2 m).2) ∈ T ∧
  (c.1 - (e2 m).1, c.2 - (e2 m).2) ∈ T

private theorem isFull_of_e2 {m : ℕ} (hm : 1 ≤ m) {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T)
    {c : ℤ × ℤ} (hc : c ∈ T) (he2 : (c.1 + (e2 m).1, c.2 + (e2 m).2) ∈ T) :
    IsFull m T c := by
  have hr := tiling_rule hm hT hc
  have h1 := hr.1 he2
  have h3 := hr.2.2.2 h1
  have h2 := hr.2.2.1 h3
  exact ⟨hc, h1, h2, he2, h3⟩

private theorem isFull_of_neg_e2 {m : ℕ} (hm : 1 ≤ m) {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T)
    {c : ℤ × ℤ} (hc : c ∈ T) (he2 : (c.1 - (e2 m).1, c.2 - (e2 m).2) ∈ T) :
    IsFull m T c := by
  have hr := tiling_rule hm hT hc
  have h1 := hr.2.2.1 he2
  have h2 := hr.2.1 h1
  have h3 := hr.1 h2
  exact ⟨hc, h3, h1, h2, he2⟩

private theorem isFull_of_e1 {m : ℕ} (hm : 1 ≤ m) {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T)
    {c : ℤ × ℤ} (hc : c ∈ T) (he1 : (c.1 + (e1 m).1, c.2 + (e1 m).2) ∈ T) :
    IsFull m T c := by
  have hr := tiling_rule hm hT hc
  have h3 := hr.2.2.2 he1
  have h2 := hr.2.2.1 h3
  have h4 := hr.2.1 h2
  exact ⟨hc, he1, h2, h4, h3⟩

private theorem isFull_of_neg_e1 {m : ℕ} (hm : 1 ≤ m) {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T)
    {c : ℤ × ℤ} (hc : c ∈ T) (he1 : (c.1 - (e1 m).1, c.2 - (e1 m).2) ∈ T) :
    IsFull m T c := by
  have hr := tiling_rule hm hT hc
  have h2 := hr.2.1 he1
  have h1 := hr.1 h2
  have h3 := hr.2.2.2 h1
  exact ⟨hc, h1, he1, h2, h3⟩

private theorem isFull_step_e1 {m : ℕ} (hm : 1 ≤ m) {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T)
    {c : ℤ × ℤ} (hf : IsFull m T c) :
    IsFull m T (c.1 + (e1 m).1, c.2 + (e1 m).2) := by
  apply isFull_of_neg_e1 hm hT hf.2.1
  convert hf.1 using 1; ext <;> dsimp only <;> ring

private theorem isFull_step_neg_e1 {m : ℕ} (hm : 1 ≤ m) {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T)
    {c : ℤ × ℤ} (hf : IsFull m T c) :
    IsFull m T (c.1 - (e1 m).1, c.2 - (e1 m).2) := by
  apply isFull_of_e1 hm hT hf.2.2.1
  convert hf.1 using 1; ext <;> dsimp only <;> ring

private theorem isFull_step_e2 {m : ℕ} (hm : 1 ≤ m) {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T)
    {c : ℤ × ℤ} (hf : IsFull m T c) :
    IsFull m T (c.1 + (e2 m).1, c.2 + (e2 m).2) := by
  apply isFull_of_neg_e2 hm hT hf.2.2.2.1
  convert hf.1 using 1; ext <;> dsimp only <;> ring

private theorem isFull_step_neg_e2 {m : ℕ} (hm : 1 ≤ m) {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T)
    {c : ℤ × ℤ} (hf : IsFull m T c) :
    IsFull m T (c.1 - (e2 m).1, c.2 - (e2 m).2) := by
  apply isFull_of_e2 hm hT hf.2.2.2.2
  convert hf.1 using 1; ext <;> dsimp only <;> ring

private theorem lambdaPlus_subset_of_isFull {m : ℕ} (hm : 1 ≤ m) {T : Set (ℤ × ℤ)}
    (hT : IsLeeTiling m T) (hfO : IsFull m T (0, 0)) :
    LambdaPlus m ⊆ T := by
  have step_i : ∀ i : ℤ, IsFull m T (i * ((m : ℤ) + 1), i * (m : ℤ)) := by
    intro i
    rcases Int.eq_nat_or_neg i with ⟨k, rfl | rfl⟩
    · induction k with
      | zero => simpa using hfO
      | succ k ih =>
        have hstep := isFull_step_e1 hm hT ih
        convert hstep using 1
        unfold e1; ext <;> push_cast <;> ring
    · induction k with
      | zero => simpa using hfO
      | succ k ih =>
        have hstep := isFull_step_neg_e1 hm hT ih
        convert hstep using 1
        unfold e1; ext <;> push_cast <;> ring
  have step_ij : ∀ i j : ℤ,
      IsFull m T (i * ((m : ℤ) + 1) - j * (m : ℤ), i * (m : ℤ) + j * ((m : ℤ) + 1)) := by
    intro i j
    rcases Int.eq_nat_or_neg j with ⟨k, rfl | rfl⟩
    · induction k with
      | zero => simpa using step_i i
      | succ k ih =>
        have hstep := isFull_step_e2 hm hT ih
        convert hstep using 1
        unfold e2; ext <;> push_cast <;> ring
    · induction k with
      | zero => simpa using step_i i
      | succ k ih =>
        have hstep := isFull_step_neg_e2 hm hT ih
        convert hstep using 1
        unfold e2; ext <;> push_cast <;> ring
  rintro z ⟨i, j, rfl⟩
  exact (step_ij i j).1

private theorem tiling_start_nonneg {m : ℕ} (hm : 1 ≤ m) {T : Set (ℤ × ℤ)}
    (hT : IsLeeTiling m T) (hO : (0, 0) ∈ T) {a : ℤ}
    (ha0 : 0 ≤ a) (ham : a ≤ (m : ℤ) - 1)
    (hc' : (a, 2 * (m : ℤ) + 1 - a) ∈ T) : False := by
  let c' : ℤ × ℤ := (a, 2 * (m : ℤ) + 1 - a)
  let v : ℤ × ℤ := (-1, (m : ℤ))
  obtain ⟨c'', hc'', hvsph⟩ := hT.2 v
  have hneO : c'' ≠ (0, 0) := by
    rintro rfl
    change taxicabDist (0, 0) v ≤ (m : ℤ) at hvsph
    unfold taxicabDist v at hvsph; dsimp only at hvsph
    rw [abs_of_pos (by omega), abs_of_nonpos (by omega)] at hvsph
    omega
  have hnec' : c'' ≠ c' := by
    rintro rfl
    change taxicabDist c' v ≤ (m : ℤ) at hvsph
    unfold taxicabDist c' v at hvsph; dsimp only at hvsph
    rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)] at hvsph
    omega
  have hdO := (sphere_disjoint_iff m c'' (0, 0)).mp (hT.1 c'' hc'' (0, 0) hO hneO)
  have hdc' := (sphere_disjoint_iff m c'' c').mp (hT.1 c'' hc'' c' hc' hnec')
  change taxicabDist c'' v ≤ (m : ℤ) at hvsph
  let al := c''.1 + 1
  let be := c''.2 - (m : ℤ)
  have hc''_eq : c'' = (-1 + al, (m : ℤ) + be) := by ext <;> dsimp [al, be] <;> ring
  rw [hc''_eq] at hvsph hdO hdc'
  unfold taxicabDist at hvsph hdO hdc'
  dsimp only [v, c'] at hvsph hdO hdc'
  have hsp2 : |al| + |be| ≤ (m : ℤ) := by
    have e1 : (-1 + al) - -1 = al := by ring
    have e2 : ((m : ℤ) + be) - (m : ℤ) = be := by ring
    rwa [e1, e2] at hvsph
  have hdo2 : 2 * (m : ℤ) + 1 ≤ |-1 + al| + |(m : ℤ) + be| := by simpa using hdO
  have hdc2 : 2 * (m : ℤ) + 1 ≤ |-1 + al - a| + |(m : ℤ) + be - (2 * (m : ℤ) + 1 - a)| := hdc'
  have hal_m : al = -(m : ℤ) ∧ be = 0 := by
    rcases le_or_gt 0 al with h1 | h1 <;>
    rcases le_or_gt 0 be with h2 | h2 <;>
    rcases le_or_gt 0 (-1 + al) with h3 | h3 <;>
    rcases le_or_gt 0 ((m : ℤ) + be) with h4 | h4 <;>
    rcases le_or_gt 0 (-1 + al - a) with h5 | h5 <;>
    rcases le_or_gt 0 ((m : ℤ) + be - (2 * (m : ℤ) + 1 - a)) with h6 | h6 <;>
    (simp only [abs_of_nonneg, abs_of_neg, *] at hsp2 hdo2 hdc2
     try (omega))
  have hc''_val : c'' = (-(m : ℤ) - 1, (m : ℤ)) := by
    rw [hc''_eq, hal_m.1, hal_m.2]; ext <;> ring
  -- Now z = (-1, m + 1)
  let z : ℤ × ℤ := (-1, (m : ℤ) + 1)
  obtain ⟨c''', hc''', hzsph⟩ := hT.2 z
  have hnec'' : c''' ≠ c'' := by
    intro heq
    change taxicabDist c''' z ≤ (m : ℤ) at hzsph
    rw [heq, hc''_val] at hzsph
    unfold taxicabDist at hzsph; dsimp only [z] at hzsph
    rw [abs_of_neg (by omega), abs_of_neg (by omega)] at hzsph
    omega
  have hnec'3 : c''' ≠ c' := by
    rintro rfl
    change taxicabDist c' z ≤ (m : ℤ) at hzsph
    unfold taxicabDist c' z at hzsph; dsimp only at hzsph
    rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)] at hzsph
    omega
  have hdc''3 := (sphere_disjoint_iff m c''' c'').mp (hT.1 c''' hc''' c'' hc'' hnec'')
  have hdc'3 := (sphere_disjoint_iff m c''' c').mp (hT.1 c''' hc''' c' hc' hnec'3)
  change taxicabDist c''' z ≤ (m : ℤ) at hzsph
  let al3 := c'''.1 + 1
  let be3 := c'''.2 - ((m : ℤ) + 1)
  have hc'''_eq : c''' = (-1 + al3, (m : ℤ) + 1 + be3) := by ext <;> dsimp [al3, be3] <;> ring
  rw [hc'''_eq, hc''_val] at hdc''3
  rw [hc'''_eq] at hzsph hdc'3
  unfold taxicabDist at hzsph hdc''3 hdc'3
  dsimp only [z, c'] at hzsph hdc''3 hdc'3
  have hsp3 : |al3| + |be3| ≤ (m : ℤ) := by
    have e1 : (-1 + al3) - -1 = al3 := by ring
    have e2 : ((m : ℤ) + 1 + be3) - ((m : ℤ) + 1) = be3 := by ring
    rwa [e1, e2] at hzsph
  have hdc3a : 2 * (m : ℤ) + 1 ≤ |al3 + (m : ℤ)| + |1 + be3| := by
    have e1 : (-1 + al3) - (-(m : ℤ) - 1) = al3 + (m : ℤ) := by ring
    have e2 : ((m : ℤ) + 1 + be3) - (m : ℤ) = 1 + be3 := by ring
    rwa [e1, e2] at hdc''3
  have hdc3b : 2 * (m : ℤ) + 1 ≤ |al3 - 1 - a| + |a - (m : ℤ) + be3| := by
    have e1 : (-1 + al3) - a = al3 - 1 - a := by ring
    have e2 : ((m : ℤ) + 1 + be3) - (2 * (m : ℤ) + 1 - a) = a - (m : ℤ) + be3 := by ring
    rwa [e1, e2] at hdc'3
  rcases le_or_gt 0 al3 with h1 | h1 <;>
  rcases le_or_gt 0 be3 with h2 | h2 <;>
  rcases le_or_gt 0 (al3 + (m : ℤ)) with h3 | h3 <;>
  rcases le_or_gt 0 (1 + be3) with h4 | h4 <;>
  rcases le_or_gt 0 (al3 - 1 - a) with h5 | h5 <;>
  rcases le_or_gt 0 (a - (m : ℤ) + be3) with h6 | h6 <;>
  (simp only [abs_of_nonneg, abs_of_neg, *] at hsp3 hdc3a hdc3b
   omega)

private theorem tiling_start {m : ℕ} (hm : 1 ≤ m) {T : Set (ℤ × ℤ)} (hT : IsLeeTiling m T)
    (hO : (0, 0) ∈ T) :
    e2 m ∈ T ∨ ((m : ℤ), (m : ℤ) + 1) ∈ T := by
  let u : ℤ × ℤ := (0, (m : ℤ) + 1)
  obtain ⟨c', hc', husph⟩ := hT.2 u
  have hneO : c' ≠ (0, 0) := by
    rintro rfl
    change taxicabDist (0, 0) u ≤ (m : ℤ) at husph
    unfold taxicabDist at husph; dsimp only [u] at husph
    rw [sub_self, abs_zero, zero_add, zero_sub, abs_neg, abs_of_pos (by omega)] at husph
    omega
  have hdO := (sphere_disjoint_iff m c' (0, 0)).mp (hT.1 c' hc' (0, 0) hO hneO)
  change taxicabDist c' u ≤ (m : ℤ) at husph
  let a := c'.1
  let b := c'.2 - ((m : ℤ) + 1)
  have hc'_eq : c' = (a, (m : ℤ) + 1 + b) := by ext <;> dsimp [a, b] <;> ring
  rw [hc'_eq] at husph hdO
  unfold taxicabDist at husph hdO
  dsimp only [u] at husph hdO
  have hsp : |a| + |b| ≤ (m : ℤ) := by
    have e1 : a - 0 = a := by ring
    have e2 : ((m : ℤ) + 1 + b) - ((m : ℤ) + 1) = b := by ring
    rwa [e1, e2] at husph
  have hd1 : 2 * (m : ℤ) + 1 ≤ |a| + |(m : ℤ) + 1 + b| := by simpa using hdO
  have hb_eq : 0 ≤ b ∧ |a| + b = (m : ℤ) := by
    have htri : |(m : ℤ) + 1 + b| ≤ (m : ℤ) + 1 + |b| := by
      calc |(m : ℤ) + 1 + b| ≤ |(m : ℤ) + 1| + |b| := abs_add_le _ _
        _ = (m : ℤ) + 1 + |b| := by rw [abs_of_pos (by omega)]
    have h1 : |a| + |b| = (m : ℤ) := by linarith
    have h2 : |(m : ℤ) + 1 + b| = (m : ℤ) + 1 + |b| := by linarith
    rcases le_or_gt 0 b with hb0 | hb0
    · rw [abs_of_nonneg hb0] at h1; exact ⟨hb0, h1⟩
    · exfalso
      rw [abs_of_neg hb0] at h2
      rcases le_or_gt 0 ((m : ℤ) + 1 + b) with hmb | hmb
      · rw [abs_of_nonneg hmb] at h2; omega
      · rw [abs_of_neg hmb] at h2; omega
  by_cases ha_abs : |a| = (m : ℤ)
  · have hb0 : b = 0 := by omega
    rcases le_or_gt 0 a with ha0 | ha0
    · right
      rw [abs_of_nonneg ha0] at ha_abs
      have heq : c' = ((m : ℤ), (m : ℤ) + 1) := by rw [hc'_eq, ha_abs, hb0]; ext <;> ring
      rwa [← heq]
    · left
      rw [abs_of_neg ha0] at ha_abs
      have heq : c' = e2 m := by rw [hc'_eq]; unfold e2; ext <;> dsimp only <;> omega
      rwa [← heq]
  · exfalso
    have hlt : |a| ≤ (m : ℤ) - 1 := by omega
    rcases le_or_gt 0 a with ha0 | ha0
    · rw [abs_of_nonneg ha0] at hlt hb_eq
      have hc'_val : c' = (a, 2 * (m : ℤ) + 1 - a) := by
        rw [hc'_eq]; ext <;> dsimp only <;> omega
      rw [hc'_val] at hc'
      exact tiling_start_nonneg hm hT hO ha0 hlt hc'
    · rw [abs_of_neg ha0] at hlt hb_eq
      let Tm : Set (ℤ × ℤ) := { p | (-p.1, p.2) ∈ T }
      have hTm : IsLeeTiling m Tm := isLeeTiling_mirrorX hT
      have hOm : (0, 0) ∈ Tm := by simpa [Tm] using hO
      have hc'_m : (-a, 2 * (m : ℤ) + 1 - (-a)) ∈ Tm := by
        change (-(-a), 2 * (m : ℤ) + 1 - (-a)) ∈ T
        have heq : (-(-a), 2 * (m : ℤ) + 1 - (-a)) = c' := by
          rw [hc'_eq]; ext <;> dsimp only <;> omega
        rwa [heq]
      exact tiling_start_nonneg hm hTm hOm (by omega) hlt hc'_m

/-- **Claim 7:** Every radius-`m` Lee tiling of `ℤ^2` containing `(0, 0)` equals `LambdaPlus m`
or `LambdaMinus m`. -/
theorem claim7_lee_tiling_classification (m : ℕ) (hm : 1 ≤ m) (T : Set (ℤ × ℤ))
    (hT : IsLeeTiling m T) (hO : (0, 0) ∈ T) :
    T = LambdaPlus m ∨ T = LambdaMinus m := by
  have hcase : ∀ T' : Set (ℤ × ℤ), IsLeeTiling m T' → (0, 0) ∈ T' → e2 m ∈ T' →
      T' = LambdaPlus m := by
    intro T' hT' hO' he2'
    have hsub : LambdaPlus m ⊆ T' :=
      lambdaPlus_subset_of_isFull hm hT' (isFull_of_e2 hm hT' hO' (by simpa using he2'))
    refine Set.Subset.antisymm ?_ hsub
    intro c hc
    obtain ⟨c₀, hc₀, hsph⟩ := (LambdaPlus_isLeeTiling hm).2 c
    by_contra hnc
    have hne : c ≠ c₀ := fun h => hnc (h ▸ hc₀)
    have hdisj := hT'.1 c hc c₀ (hsub hc₀) hne
    refine Set.disjoint_left.mp hdisj ?_ hsph
    change taxicabDist c c ≤ (m : ℤ)
    rw [taxicabDist_self]
    omega
  rcases tiling_start hm hT hO with he2 | hm1
  · exact Or.inl (hcase T hT hO he2)
  · right
    let Tm := { p : ℤ × ℤ | (-p.1, p.2) ∈ T }
    have hTm : IsLeeTiling m Tm := isLeeTiling_mirrorX hT
    have hOm : (0, 0) ∈ Tm := by simpa [Tm] using hO
    have he2m : e2 m ∈ Tm := by
      change (-(-(m : ℤ)), (m : ℤ) + 1) ∈ T
      simpa using hm1
    have hTm_eq := hcase Tm hTm hOm he2m
    ext ⟨x, y⟩
    have hmem : (-x, y) ∈ Tm ↔ (-x, y) ∈ LambdaPlus m := by rw [hTm_eq]
    have hm1' : (-x, y) ∈ Tm ↔ (x, y) ∈ T := by simp [Tm]
    have hm2' : (-x, y) ∈ LambdaPlus m ↔ (x, y) ∈ LambdaMinus m := by
      rw [mem_LambdaPlus_iff_dvd, mem_LambdaMinus_iff_dvd]
      dsimp only; ring_nf
    exact hm1'.symm.trans (hmem.trans hm2')

/-! ## Section 4: Step 8 — Validity of `sigmaPlus`/`sigmaMinus` and Equivalence -/

theorem plotPoint_sigmaPlus_mem_LambdaPlus {m : ℕ} (hm : 1 ≤ m) (i : Fin (n_odd m)) :
    plotPoint (sigmaPlus m) i ∈ LambdaPlus m := by
  rw [mem_LambdaPlus_iff_dvd]
  exact (sigmaPlus_mod_eq hm i).symm.dvd

theorem plotPoint_sigmaMinus_mem_LambdaMinus {m : ℕ} (hm : 1 ≤ m) (i : Fin (n_odd m)) :
    plotPoint (sigmaMinus m) i ∈ LambdaMinus m := by
  rw [mem_LambdaMinus_iff_dvd]
  have hmod := sigmaMinus_mod_eq hm i
  have heq : (((sigmaMinus m i).val : ℤ) + 1) + (d_odd m : ℤ) * ((i.val : ℤ) + 1) =
      (((sigmaMinus m i).val : ℤ) + 1) - -((d_odd m : ℤ) * ((i.val : ℤ) + 1)) := by ring
  unfold plotPoint; dsimp only; rw [heq]
  exact hmod.symm.dvd

theorem LambdaMinus_dist {m : ℕ} (hm : 1 ≤ m) {p q : ℤ × ℤ}
    (hp : p ∈ LambdaMinus m) (hq : q ∈ LambdaMinus m) (hpq : p ≠ q) :
    2 * (m : ℤ) + 1 ≤ taxicabDist p q := by
  have hp' : (-p.1, p.2) ∈ LambdaPlus m := by
    rw [mem_LambdaPlus_iff_dvd]; rw [mem_LambdaMinus_iff_dvd] at hp
    simpa [mul_neg, sub_neg_eq_add] using hp
  have hq' : (-q.1, q.2) ∈ LambdaPlus m := by
    rw [mem_LambdaPlus_iff_dvd]; rw [mem_LambdaMinus_iff_dvd] at hq
    simpa [mul_neg, sub_neg_eq_add] using hq
  have hne' : (-p.1, p.2) ≠ (-q.1, q.2) := by
    intro h; apply hpq; exact Prod.ext (by have := (Prod.mk.inj h).1; omega) (Prod.mk.inj h).2
  have hd := LambdaPlus_dist hm hp' hq' hne'
  have heq : taxicabDist (-p.1, p.2) (-q.1, q.2) = taxicabDist p q := by
    unfold taxicabDist; dsimp only
    have h1 : |-p.1 - -q.1| = |p.1 - q.1| := by rw [← abs_neg]; ring_nf
    rw [h1]
  rwa [← heq]

theorem sigmaPlus_isValidOdd {m : ℕ} (hm : 1 ≤ m) : IsValidOdd m (sigmaPlus m) := by
  intro i j hij
  unfold d_odd
  exact_mod_cast LambdaPlus_dist hm
    (plotPoint_sigmaPlus_mem_LambdaPlus hm i)
    (plotPoint_sigmaPlus_mem_LambdaPlus hm j)
    (fun h => hij (plotPoint_injective _ h))

theorem sigmaMinus_isValidOdd {m : ℕ} (hm : 1 ≤ m) : IsValidOdd m (sigmaMinus m) := by
  intro i j hij
  unfold d_odd
  exact_mod_cast LambdaMinus_dist hm
    (plotPoint_sigmaMinus_mem_LambdaMinus hm i)
    (plotPoint_sigmaMinus_mem_LambdaMinus hm j)
    (fun h => hij (plotPoint_injective _ h))

theorem validOdd_eq_sigmaPlus_or_sigmaMinus {m : ℕ} (hm : 1 ≤ m)
    {w : Equiv.Perm (Fin (n_odd m))} (hw : IsValidOdd m w) :
    w = sigmaPlus m ∨ w = sigmaMinus m := by
  have ⟨htil, hO⟩ := claim6_torus_tiling hm hw
  rcases claim7_lee_tiling_classification m hm (torusCenters m w) htil hO with hP | hM
  · left
    ext i
    have hmem : plotPoint w i ∈ LambdaPlus m := by
      rw [← hP]
      exact ⟨plotPoint w i, Set.mem_insert_of_mem _ ⟨i, rfl⟩, 0, 0, by simp⟩
    rw [mem_LambdaPlus_iff_dvd] at hmem
    have hmod : (((w i).val : ℤ) + 1) ≡ (d_odd m : ℤ) * ((i.val : ℤ) + 1) [ZMOD (N_odd m : ℤ)] :=
      (Int.modEq_iff_dvd.mpr hmem).symm
    have hplus := (sigmaPlus_mod_eq hm i).symm
    have heq_mod := hmod.trans hplus
    have hN1 : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
    have hb1 : 0 ≤ ((w i).val : ℤ) + 1 ∧ ((w i).val : ℤ) + 1 < (N_odd m : ℤ) := by
      have := (w i).isLt; omega
    have hb2 : 0 ≤ ((sigmaPlus m i).val : ℤ) + 1 ∧ ((sigmaPlus m i).val : ℤ) + 1 < (N_odd m : ℤ) := by
      have := (sigmaPlus m i).isLt; omega
    have hz : ((w i).val : ℤ) + 1 = ((sigmaPlus m i).val : ℤ) + 1 := by
      rw [Int.ModEq, Int.emod_eq_of_lt hb1.1 hb1.2, Int.emod_eq_of_lt hb2.1 hb2.2] at heq_mod
      exact heq_mod
    omega
  · right
    ext i
    have hmem : plotPoint w i ∈ LambdaMinus m := by
      rw [← hM]
      exact ⟨plotPoint w i, Set.mem_insert_of_mem _ ⟨i, rfl⟩, 0, 0, by simp⟩
    rw [mem_LambdaMinus_iff_dvd] at hmem
    have hmod : (((w i).val : ℤ) + 1) ≡ -((d_odd m : ℤ) * ((i.val : ℤ) + 1)) [ZMOD (N_odd m : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      have heq : -((d_odd m : ℤ) * ((i.val : ℤ) + 1)) - (((w i).val : ℤ) + 1) =
          -((((w i).val : ℤ) + 1) + (d_odd m : ℤ) * ((i.val : ℤ) + 1)) := by ring
      rw [heq]
      exact dvd_neg.mpr hmem
    have hminus := (sigmaMinus_mod_eq hm i).symm
    have heq_mod := hmod.trans hminus
    have hN1 : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
    have hb1 : 0 ≤ ((w i).val : ℤ) + 1 ∧ ((w i).val : ℤ) + 1 < (N_odd m : ℤ) := by
      have := (w i).isLt; omega
    have hb2 : 0 ≤ ((sigmaMinus m i).val : ℤ) + 1 ∧ ((sigmaMinus m i).val : ℤ) + 1 < (N_odd m : ℤ) := by
      have := (sigmaMinus m i).isLt; omega
    have hz : ((w i).val : ℤ) + 1 = ((sigmaMinus m i).val : ℤ) + 1 := by
      rw [Int.ModEq, Int.emod_eq_of_lt hb1.1 hb1.2, Int.emod_eq_of_lt hb2.1 hb2.2] at heq_mod
      exact heq_mod
    omega

end MinimalProlific
