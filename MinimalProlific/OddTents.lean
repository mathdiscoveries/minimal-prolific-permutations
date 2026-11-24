module

public import MinimalProlific.Defs
public import Mathlib.Data.Fintype.Sum

import Mathlib.Tactic

/-!
# Steps 0–5 of Theorem A (`MinimalProlific.OddTents`)

Formalizes Steps 0 through 5 of `03a_theorem_odd.md` for every `m ≥ 1` and every valid
permutation `w : Equiv.Perm (Fin (n_odd m))`:
- **Step 0 (`sphere_disjoint_iff`, `colCover_card_of_mem_centralSet`)**: Lee spheres `S(p)` and
  `S(q)` are disjoint iff `|p - q| ≥ 2m + 1`; each central column `x ∈ C` has `N` covered cells.
- **Step 1 (`claim1_supports_partition`, Consequences 1a–1d)**: The `2m` top and bottom supports
  `A_t, B_t` are pairwise disjoint and partition `C = [m + 1, n - m]`; overhang bounds,
  central-column hole count `g(x) - 1`, no outside coverage for side columns, and all plot points
  lie at distance `≥ 2m + 1` from every corner `(0,0), (N,0), (0,N), (N,N)`.
- **Step 2 (`claim2_left_side_col_holes`, etc.)**: Side column/row `m + 1 - s` (`1 ≤ s ≤ m`) has
  exactly `s^2 - 1` holes; in particular columns/rows `m` and `N - m` have zero holes.
- **Step 3 (`claim3_corners`, `claim3a_corner_square_00`)**: Exactly one of `(m + 1, m), (m, m + 1)`
  (and symmetrically at each corner) is in the plot, and `[1, m]^2` holes are `{x + y ≤ m}`.
- **Step 4 (`claim4_central_box_covered`)**: Every cell of `C × C` is covered (zero holes).
- **Step 5 (`claim5_central_col_holes`)**: For `x ∈ C`, the `g(x) - 1` holes sit at rows
  `1 .. g(x) - 1` if `x` is of top type, and at rows `N - (g(x) - 1) .. n` if of bottom type.
-/

@[expose] public section

namespace MinimalProlific

open Finset

/-! ## Section 1: Step 0 — Disjointness and Vertical Chords -/

/-- **(0a) Disjointness:** Two radius-`m` Lee spheres are disjoint iff their centers have
taxicab distance at least `2m + 1`. -/
theorem sphere_disjoint_iff (m : ℕ) (p q : ℤ × ℤ) :
    Disjoint (leeSphere m p) (leeSphere m q) ↔ (2 * (m : ℤ) + 1) ≤ taxicabDist p q := by
  rw [Set.disjoint_left]
  constructor
  · intro hdisj
    by_contra hlt
    have hle : taxicabDist p q ≤ 2 * (m : ℤ) := by omega
    unfold taxicabDist at hle
    let dx := q.1 - p.1
    let dy := q.2 - p.2
    have hdx_dy : |dx| + |dy| ≤ 2 * (m : ℤ) := by
      change |q.1 - p.1| + |q.2 - p.2| ≤ 2 * (m : ℤ)
      rw [abs_sub_comm q.1 p.1, abs_sub_comm q.2 p.2]
      exact hle
    by_cases hdx : |dx| ≤ (m : ℤ)
    · let r : ℤ := (m : ℤ) - |dx|
      by_cases hdy : |dy| ≤ r
      · apply hdisj (a := q)
        · change taxicabDist p q ≤ (m : ℤ)
          unfold taxicabDist
          rw [abs_sub_comm p.1 q.1, abs_sub_comm p.2 q.2]
          change |dx| + |dy| ≤ (m : ℤ)
          omega
        · change taxicabDist q q ≤ (m : ℤ)
          rw [taxicabDist_self]
          omega
      · let z : ℤ × ℤ := (q.1, p.2 + (if 0 ≤ dy then r else -r))
        apply hdisj (a := z)
        · change |p.1 - q.1| + |p.2 - (p.2 + (if 0 ≤ dy then r else -r))| ≤ (m : ℤ)
          have hpq : |p.1 - q.1| = |dx| := by dsimp [dx]; rw [abs_sub_comm]
          have hsubp : p.2 - (p.2 + (if 0 ≤ dy then r else -r)) = -(if 0 ≤ dy then r else -r) := by
            ring
          rw [hpq, hsubp, abs_neg]
          split_ifs
          · rw [abs_of_nonneg (by omega : 0 ≤ r)]
            omega
          · rw [abs_neg, abs_of_nonneg (by omega : 0 ≤ r)]
            omega
        · change |q.1 - q.1| + |q.2 - (p.2 + (if 0 ≤ dy then r else -r))| ≤ (m : ℤ)
          rw [sub_self, abs_zero, zero_add]
          have hsub : q.2 - (p.2 + (if 0 ≤ dy then r else -r)) =
              dy - (if 0 ≤ dy then r else -r) := by dsimp [dy]; ring
          rw [hsub]
          split_ifs with h0
          · rw [abs_of_nonneg h0] at hdy hdx_dy
            rw [abs_of_nonneg (by omega)]
            omega
          · rw [abs_of_neg (not_le.mp h0)] at hdy hdx_dy
            rw [abs_of_neg (by omega)]
            omega
    · let z : ℤ × ℤ := (p.1 + (if 0 ≤ dx then (m : ℤ) else -(m : ℤ)), p.2)
      apply hdisj (a := z)
      · change |p.1 - (p.1 + (if 0 ≤ dx then (m : ℤ) else -(m : ℤ)))| + |p.2 - p.2| ≤ (m : ℤ)
        rw [sub_self, abs_zero, add_zero]
        have hsub : p.1 - (p.1 + (if 0 ≤ dx then (m : ℤ) else -(m : ℤ))) =
            -(if 0 ≤ dx then (m : ℤ) else -(m : ℤ)) := by ring
        rw [hsub, abs_neg]
        split_ifs <;> simp
      · change |q.1 - (p.1 + (if 0 ≤ dx then (m : ℤ) else -(m : ℤ)))| + |q.2 - p.2| ≤ (m : ℤ)
        have hsub : q.1 - (p.1 + (if 0 ≤ dx then (m : ℤ) else -(m : ℤ))) =
            dx - (if 0 ≤ dx then (m : ℤ) else -(m : ℤ)) := by dsimp [dx]; ring
        rw [hsub]
        change |dx - (if 0 ≤ dx then (m : ℤ) else -(m : ℤ))| + |dy| ≤ (m : ℤ)
        split_ifs with h0
        · rw [abs_of_nonneg h0] at hdx hdx_dy
          rw [abs_of_nonneg (by omega)]
          omega
        · rw [abs_of_neg (not_le.mp h0)] at hdx hdx_dy
          rw [abs_of_neg (by omega)]
          omega
  · intro hdist z hzp hzq
    change taxicabDist p z ≤ (m : ℤ) at hzp
    change taxicabDist q z ≤ (m : ℤ) at hzq
    have htri := taxicabDist_triangle p z q
    rw [taxicabDist_comm z q] at htri
    omega

theorem isValidOdd_iff_spheres_disjoint {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) :
    IsValidOdd m w ↔
      ∀ i j : Fin (n_odd m), i ≠ j →
        Disjoint (leeSphere m (plotPoint w i)) (leeSphere m (plotPoint w j)) := by
  unfold IsValidOdd IsValidPerm d_odd
  constructor
  · intro h i j hij
    rw [sphere_disjoint_iff]
    exact_mod_cast h i j hij
  · intro h i j hij
    have hd := (sphere_disjoint_iff m (plotPoint w i) (plotPoint w j)).mp (h i j hij)
    exact_mod_cast hd

/-- The `y`-coordinates of column `x` covered by `plot w`. -/
def colCover (m : ℕ) (w : Equiv.Perm (Fin (n_odd m))) (x : ℤ) : Finset ℤ :=
  Finset.univ.biUnion (fun i => sphereColFinset m (plotPoint w i) x)

theorem mem_colCover {m : ℕ} {w : Equiv.Perm (Fin (n_odd m))} {x y : ℤ} :
    y ∈ colCover m w x ↔ isCovered m w (x, y) := by
  unfold colCover isCovered
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_sphereColFinset]

theorem colCover_card_eq_sum {m : ℕ} {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) (x : ℤ) :
    (colCover m w x).card =
      ∑ i : Fin (n_odd m), (sphereColFinset m (plotPoint w i) x).card := by
  unfold colCover
  rw [Finset.card_biUnion]
  intro i _ j _ hij
  refine Finset.disjoint_left.mpr fun y hyi hyj => ?_
  rw [mem_sphereColFinset] at hyi hyj
  have hdisj := (isValidOdd_iff_spheres_disjoint w).mp hw i j hij
  exact Set.disjoint_left.mp hdisj hyi hyj

/-- Central columns (and central rows) `C = {m + 1, ..., n - m}`. -/
def centralSet (m : ℕ) : Finset ℤ :=
  Finset.Icc ((m : ℤ) + 1) ((n_odd m : ℤ) - (m : ℤ))

theorem centralSet_card (m : ℕ) : (centralSet m).card = 2 * m ^ 2 := by
  unfold centralSet n_odd
  rw [Int.card_Icc]
  have h : (2 * (m : ℤ) ^ 2 + 2 * (m : ℤ) - (m : ℤ)) + 1 - ((m : ℤ) + 1) = 2 * (m : ℤ) ^ 2 := by
    ring
  push_cast
  rw [h]
  have h0 : (0 : ℤ) ≤ 2 * (m : ℤ) ^ 2 := by positivity
  exact_mod_cast Int.toNat_of_nonneg h0

theorem mem_centralSet_iff {m : ℕ} {x : ℤ} :
    x ∈ centralSet m ↔ (m : ℤ) + 1 ≤ x ∧ x ≤ (n_odd m : ℤ) - (m : ℤ) := by
  unfold centralSet
  exact Finset.mem_Icc

theorem colCover_card_of_mem_centralSet {m : ℕ} (hm : 1 ≤ m)
    {w : Equiv.Perm (Fin (n_odd m))} (hw : IsValidOdd m w) {x : ℤ} (hx : x ∈ centralSet m) :
    (colCover m w x).card = N_odd m := by
  rw [mem_centralSet_iff] at hx
  rw [colCover_card_eq_sum hw x]
  have h2m := two_mul_m_le_n_odd hm
  have hsplit : ∑ i : Fin (n_odd m), (sphereColFinset m (plotPoint w i) x).card =
      ∑ i ∈ (Finset.univ : Finset (Fin (n_odd m))).filter
          (fun i => (x - ((i.val : ℤ) + 1)).natAbs ≤ m),
        (2 * (m - (x - ((i.val : ℤ) + 1)).natAbs) + 1) := by
    rw [← Finset.sum_subset (Finset.filter_subset
        (fun i : Fin (n_odd m) => (x - ((i.val : ℤ) + 1)).natAbs ≤ m) Finset.univ)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_filter] at hi
      rw [card_sphereColFinset]
      unfold plotPoint
      simp [hi.2]
    · intro i _ hnot
      rw [Finset.mem_filter, not_and] at hnot
      have hgt : ¬ (x - ((i.val : ℤ) + 1)).natAbs ≤ m := fun h => hnot (Finset.mem_univ _) h
      rw [card_sphereColFinset]
      unfold plotPoint
      simp [hgt]
  rw [hsplit]
  have hbij :
      ∑ i ∈ Finset.univ.filter (fun i : Fin (n_odd m) => (x - ((i.val : ℤ) + 1)).natAbs ≤ m),
        (2 * (m - (x - ((i.val : ℤ) + 1)).natAbs) + 1) =
      ∑ j ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), (2 * (m - j.natAbs) + 1) := by
    refine Finset.sum_bij (fun i _ => x - ((i.val : ℤ) + 1)) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_Icc]
      omega
    · intro i₁ _ i₂ _ h
      exact Fin.ext (by omega)
    · intro j hj
      rw [Finset.mem_Icc] at hj
      have hc : 1 ≤ x - j ∧ x - j ≤ (n_odd m : ℤ) := by omega
      refine ⟨⟨(x - j - 1).toNat, by omega⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        dsimp only
        have heq : x - (((x - j - 1).toNat : ℤ) + 1) = j := by omega
        rw [heq]
        omega
      · dsimp only; omega
    · intro i _; rfl
  rw [hbij, sum_chord_Icc]
  rfl

/-! ## Section 2: Step 1 — Top/Bottom Supports Partition `C` (Claim 1 & 1a–1d) -/

/-- Helper: `∑_{t < m} (2*(m - t) - 1) = m^2`. -/
private theorem sum_fin_tent_width (m : ℕ) :
    ∑ t : Fin m, (2 * (m - t.val) - 1) = m ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.succ_sub_succ_eq_sub]
    rw [ih]
    have h1 : 1 ≤ 2 * (m + 1) := by omega
    zify [h1]
    ring

/-- Helper: if `(S.biUnion f).card = ∑ s ∈ S, (f s).card`, then `f` is pairwise disjoint on `S`. -/
private theorem pairwiseDisjoint_of_card_biUnion_eq_sum {α β : Type*} [DecidableEq α]
    [DecidableEq β] (S : Finset α) (f : α → Finset β)
    (heq : (S.biUnion f).card = ∑ s ∈ S, (f s).card) :
    (S : Set α).PairwiseDisjoint f := by
  induction S using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha] at heq
    have hcard := Finset.card_union_add_card_inter (f a) (s.biUnion f)
    have hle : (s.biUnion f).card ≤ ∑ x ∈ s, (f x).card := Finset.card_biUnion_le
    have hinter0 : (f a ∩ s.biUnion f).card = 0 := by omega
    have hsub_eq : (s.biUnion f).card = ∑ x ∈ s, (f x).card := by omega
    have hdisj_a : Disjoint (f a) (s.biUnion f) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hinter0)
    have hsub_pd := ih hsub_eq
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem f hy) hdisj_a
    · exact (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem f hx) hdisj_a).symm
    · exact hsub_pd hx hy hxy

/-- Row index `n - 1 - t` (`y = n - t`) for `t : Fin m`. -/
def topRowIdx (m : ℕ) (hm : 1 ≤ m) (t : Fin m) : Fin (n_odd m) :=
  ⟨n_odd m - 1 - t.val, by
    have := two_mul_m_le_n_odd hm
    have := t.isLt
    omega⟩

/-- Row index `t` (`y = 1 + t`) for `t : Fin m`. -/
def botRowIdx (m : ℕ) (hm : 1 ≤ m) (t : Fin m) : Fin (n_odd m) :=
  ⟨t.val, by
    have := two_mul_m_le_n_odd hm
    have := t.isLt
    omega⟩

/-- Column coordinate `a_t` (`1`-indexed) of the plot point in row `n - t`. -/
def topCol (m : ℕ) (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) (t : Fin m) : ℤ :=
  ((w.symm (topRowIdx m hm t)).val : ℤ) + 1

/-- Column coordinate `b_t` (`1`-indexed) of the plot point in row `1 + t`. -/
def botCol (m : ℕ) (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) (t : Fin m) : ℤ :=
  ((w.symm (botRowIdx m hm t)).val : ℤ) + 1

/-- Tent height `h_t = m - t ≥ 1`. -/
def tentHeight (m : ℕ) (t : Fin m) : ℤ :=
  (m : ℤ) - (t.val : ℤ)

theorem tentHeight_pos {m : ℕ} (t : Fin m) : 1 ≤ tentHeight m t := by
  unfold tentHeight; have := t.isLt; omega

/-- Top support `A_t = {x ∈ ℤ : |x - a_t| ≤ h_t - 1}`. -/
def topSupport (m : ℕ) (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) (t : Fin m) : Finset ℤ :=
  Finset.Icc (topCol m hm w t - (tentHeight m t - 1)) (topCol m hm w t + (tentHeight m t - 1))

/-- Bottom support `B_t = {x ∈ ℤ : |x - b_t| ≤ h_t - 1}`. -/
def botSupport (m : ℕ) (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) (t : Fin m) : Finset ℤ :=
  Finset.Icc (botCol m hm w t - (tentHeight m t - 1)) (botCol m hm w t + (tentHeight m t - 1))

/-- Combined family of `2m` supports indexed by `Fin m ⊕ Fin m`. -/
def oddSupport (m : ℕ) (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) : Fin m ⊕ Fin m → Finset ℤ
  | .inl t => topSupport m hm w t
  | .inr t => botSupport m hm w t

theorem mem_topSupport_iff {m : ℕ} {hm : 1 ≤ m} {w : Equiv.Perm (Fin (n_odd m))}
    {t : Fin m} {x : ℤ} :
    x ∈ topSupport m hm w t ↔ |x - topCol m hm w t| ≤ tentHeight m t - 1 := by
  unfold topSupport
  rw [Finset.mem_Icc, abs_le]
  omega

theorem mem_botSupport_iff {m : ℕ} {hm : 1 ≤ m} {w : Equiv.Perm (Fin (n_odd m))}
    {t : Fin m} {x : ℤ} :
    x ∈ botSupport m hm w t ↔ |x - botCol m hm w t| ≤ tentHeight m t - 1 := by
  unfold botSupport
  rw [Finset.mem_Icc, abs_le]
  omega

theorem card_topSupport {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) (t : Fin m) :
    (topSupport m hm w t).card = 2 * (m - t.val) - 1 := by
  unfold topSupport tentHeight
  rw [Int.card_Icc]
  have ht := t.isLt
  omega

theorem card_botSupport {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) (t : Fin m) :
    (botSupport m hm w t).card = 2 * (m - t.val) - 1 := by
  unfold botSupport tentHeight
  rw [Int.card_Icc]
  have ht := t.isLt
  omega

theorem sum_card_oddSupport {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) :
    ∑ s : Fin m ⊕ Fin m, (oddSupport m hm w s).card = 2 * m ^ 2 := by
  rw [Fintype.sum_sum_type]
  simp only [oddSupport, card_topSupport, card_botSupport, sum_fin_tent_width]
  ring

theorem sphereCol_above_box {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m)))
    (i : Fin (n_odd m)) (x : ℤ) :
    (sphereColFinset m (plotPoint w i) x).filter (fun y => (n_odd m : ℤ) + 1 ≤ y) =
      if h : ∃ t : Fin m, w i = topRowIdx m hm t ∧ x ∈ topSupport m hm w t then
        let t := h.choose
        Finset.Icc ((n_odd m : ℤ) + 1) ((n_odd m : ℤ) + (tentHeight m t - |x - topCol m hm w t|))
      else ∅ := by
  split_ifs with hex
  · obtain ⟨ht1, ht2⟩ := hex.choose_spec
    have hwi : w i = topRowIdx m hm hex.choose := ht1
    have hcol : ((i.val : ℤ) + 1) = topCol m hm w hex.choose := by
      unfold topCol
      have hval : i.val = (w.symm (topRowIdx m hm hex.choose)).val :=
        congrArg Fin.val ((Equiv.eq_symm_apply w).mpr ht1)
      rw [hval]
    have hrow : (((w i).val : ℤ) + 1) = (n_odd m : ℤ) - (hex.choose.val : ℤ) := by
      have hval : (w i).val = (topRowIdx m hm hex.choose).val := congrArg Fin.val ht1
      rw [hval]
      unfold topRowIdx
      have h2m := two_mul_m_le_n_odd hm
      have hlt := hex.choose.isLt
      dsimp only; omega
    ext y
    simp only [Finset.mem_filter, mem_sphereColFinset, Finset.mem_Icc]
    unfold leeSphere taxicabDist plotPoint
    change (|((i.val : ℤ) + 1) - x| + |(((w i).val : ℤ) + 1) - y| ≤ (m : ℤ) ∧
      (n_odd m : ℤ) + 1 ≤ y) ↔ _
    rw [hcol, hrow, abs_sub_comm (topCol m hm w hex.choose) x]
    unfold tentHeight
    have h1 := mem_topSupport_iff.mp ht2
    unfold tentHeight at h1
    constructor
    · intro ⟨hdist, hy⟩
      refine ⟨hy, ?_⟩
      have ha : |((n_odd m : ℤ) - (hex.choose.val : ℤ)) - y| =
          y - ((n_odd m : ℤ) - (hex.choose.val : ℤ)) := by
        rw [abs_of_nonpos] <;> omega
      omega
    · intro ⟨hy1, hy2⟩
      refine ⟨?_, hy1⟩
      have ha : |((n_odd m : ℤ) - (hex.choose.val : ℤ)) - y| =
          y - ((n_odd m : ℤ) - (hex.choose.val : ℤ)) := by
        rw [abs_of_nonpos] <;> omega
      omega
  · ext y
    simp only [Finset.mem_filter, mem_sphereColFinset, Finset.notMem_empty, iff_false, not_and]
    intro hy_sph hy_ge
    apply hex
    change taxicabDist (plotPoint w i) (x, y) ≤ (m : ℤ) at hy_sph
    unfold taxicabDist plotPoint at hy_sph
    dsimp only at hy_sph
    have hwi_lt := (w i).isLt
    have habs : |((w i).val : ℤ) + 1 - y| = y - (((w i).val : ℤ) + 1) := by
      rw [abs_of_nonpos] <;> omega
    have hdist : |x - ((i.val : ℤ) + 1)| + (y - (((w i).val : ℤ) + 1)) ≤ (m : ℤ) := by
      rw [abs_sub_comm]; linarith
    have hle_m : (n_odd m : ℤ) - (((w i).val : ℤ) + 1) ≤ (m : ℤ) - 1 := by
      have : 0 ≤ |x - ((i.val : ℤ) + 1)| := abs_nonneg _
      omega
    let t : Fin m := ⟨n_odd m - 1 - (w i).val, by omega⟩
    have ht_eq : w i = topRowIdx m hm t := by
      ext; unfold topRowIdx; dsimp [t]; omega
    refine ⟨t, ht_eq, mem_topSupport_iff.mpr ?_⟩
    have hcol : topCol m hm w t = (i.val : ℤ) + 1 := by
      unfold topCol
      have : w.symm (topRowIdx m hm t) = i := by
        rw [← ht_eq, Equiv.symm_apply_apply]
      rw [this]
    rw [hcol]
    unfold tentHeight
    dsimp [t]
    omega

theorem sphereCol_below_box {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m)))
    (i : Fin (n_odd m)) (x : ℤ) :
    (sphereColFinset m (plotPoint w i) x).filter (fun y => y ≤ 0) =
      if h : ∃ t : Fin m, w i = botRowIdx m hm t ∧ x ∈ botSupport m hm w t then
        let t := h.choose
        Finset.Icc (1 - (tentHeight m t - |x - botCol m hm w t|)) 0
      else ∅ := by
  split_ifs with hex
  · obtain ⟨ht1, ht2⟩ := hex.choose_spec
    have hwi : w i = botRowIdx m hm hex.choose := ht1
    have hcol : ((i.val : ℤ) + 1) = botCol m hm w hex.choose := by
      unfold botCol
      have hval : i.val = (w.symm (botRowIdx m hm hex.choose)).val :=
        congrArg Fin.val ((Equiv.eq_symm_apply w).mpr ht1)
      rw [hval]
    have hrow : (((w i).val : ℤ) + 1) = 1 + (hex.choose.val : ℤ) := by
      have hval : (w i).val = (botRowIdx m hm hex.choose).val := congrArg Fin.val ht1
      rw [hval]
      unfold botRowIdx; dsimp only; omega
    ext y
    simp only [Finset.mem_filter, mem_sphereColFinset, Finset.mem_Icc]
    unfold leeSphere taxicabDist plotPoint
    change (|((i.val : ℤ) + 1) - x| + |(((w i).val : ℤ) + 1) - y| ≤ (m : ℤ) ∧ y ≤ 0) ↔ _
    rw [hcol, hrow, abs_sub_comm (botCol m hm w hex.choose) x]
    unfold tentHeight
    have h1 := mem_botSupport_iff.mp ht2
    unfold tentHeight at h1
    constructor
    · intro ⟨hdist, hy⟩
      refine ⟨?_, hy⟩
      have ha : |(1 + (hex.choose.val : ℤ)) - y| = (1 + (hex.choose.val : ℤ)) - y :=
        abs_of_nonneg (by omega)
      omega
    · intro ⟨hy1, hy2⟩
      refine ⟨?_, hy2⟩
      have ha : |(1 + (hex.choose.val : ℤ)) - y| = (1 + (hex.choose.val : ℤ)) - y :=
        abs_of_nonneg (by omega)
      omega
  · ext y
    simp only [Finset.mem_filter, mem_sphereColFinset, Finset.notMem_empty, iff_false, not_and]
    intro hy_sph hy_le
    apply hex
    change taxicabDist (plotPoint w i) (x, y) ≤ (m : ℤ) at hy_sph
    unfold taxicabDist plotPoint at hy_sph
    dsimp only at hy_sph
    have habs : |((w i).val : ℤ) + 1 - y| = ((w i).val : ℤ) + 1 - y :=
      abs_of_nonneg (by omega)
    have hdist : |x - ((i.val : ℤ) + 1)| + (((w i).val : ℤ) + 1 - y) ≤ (m : ℤ) := by
      rw [abs_sub_comm]; linarith
    have hlt_m : (w i).val < m := by
      have : 0 ≤ |x - ((i.val : ℤ) + 1)| := abs_nonneg _
      omega
    let t : Fin m := ⟨(w i).val, hlt_m⟩
    have ht_eq : w i = botRowIdx m hm t := by
      ext; unfold botRowIdx; rfl
    refine ⟨t, ht_eq, mem_botSupport_iff.mpr ?_⟩
    have hcol : botCol m hm w t = (i.val : ℤ) + 1 := by
      unfold botCol
      have : w.symm (botRowIdx m hm t) = i := by
        rw [← ht_eq, Equiv.symm_apply_apply]
      rw [this]
    rw [hcol]
    unfold tentHeight
    dsimp [t]
    omega

/-- **Claim 1:** For any valid plot `w` (`1 ≤ m`), the `2m` supports `A_0, ..., A_{m-1},
B_0, ..., B_{m-1}` are pairwise disjoint and their union equals the central columns `C`. -/
theorem claim1_supports_partition {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) :
    Finset.univ.biUnion (oddSupport m hm w) = centralSet m ∧
      (Set.univ : Set (Fin m ⊕ Fin m)).PairwiseDisjoint (oddSupport m hm w) := by
  have hsub : centralSet m ⊆ Finset.univ.biUnion (oddSupport m hm w) := by
    intro x hx
    have hcard := colCover_card_of_mem_centralSet hm hw hx
    have hnot : ¬ (colCover m w x ⊆ Finset.Icc 1 (n_odd m : ℤ)) := by
      intro hsub_box
      have hle := Finset.card_le_card hsub_box
      rw [hcard, Int.card_Icc] at hle
      have hN : N_odd m = n_odd m + 1 := (n_odd_add_one m).symm
      omega
    rw [Finset.not_subset] at hnot
    obtain ⟨y, hy_cov, hy_out⟩ := hnot
    rw [mem_colCover] at hy_cov
    obtain ⟨i, hi⟩ := hy_cov
    rw [← mem_sphereColFinset] at hi
    rw [Finset.mem_Icc] at hy_out
    have hcases : (n_odd m : ℤ) + 1 ≤ y ∨ y ≤ 0 := by omega
    rw [Finset.mem_biUnion]
    rcases hcases with hy_hi | hy_lo
    · have hne : ((sphereColFinset m (plotPoint w i) x).filter
          (fun y => (n_odd m : ℤ) + 1 ≤ y)).Nonempty :=
        ⟨y, Finset.mem_filter.mpr ⟨hi, hy_hi⟩⟩
      rw [sphereCol_above_box hm w i x] at hne
      split_ifs at hne with hex
      · obtain ⟨t, _, ht⟩ := hex
        exact ⟨.inl t, Finset.mem_univ _, ht⟩
      · exact absurd hne Finset.not_nonempty_empty
    · have hne : ((sphereColFinset m (plotPoint w i) x).filter
          (fun y => y ≤ 0)).Nonempty :=
        ⟨y, Finset.mem_filter.mpr ⟨hi, hy_lo⟩⟩
      rw [sphereCol_below_box hm w i x] at hne
      split_ifs at hne with hex
      · obtain ⟨t, _, ht⟩ := hex
        exact ⟨.inr t, Finset.mem_univ _, ht⟩
      · exact absurd hne Finset.not_nonempty_empty
  have hcard_le : (Finset.univ.biUnion (oddSupport m hm w)).card ≤
      ∑ s : Fin m ⊕ Fin m, (oddSupport m hm w s).card := Finset.card_biUnion_le
  have hcard_eq : (Finset.univ.biUnion (oddSupport m hm w)).card =
      ∑ s : Fin m ⊕ Fin m, (oddSupport m hm w s).card := by
    have h1 := Finset.card_le_card hsub
    rw [centralSet_card, ← sum_card_oddSupport hm w] at h1
    omega
  have hunion : Finset.univ.biUnion (oddSupport m hm w) = centralSet m := by
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hcard_eq, sum_card_oddSupport hm w, centralSet_card]
  have hpd := pairwiseDisjoint_of_card_biUnion_eq_sum Finset.univ (oddSupport m hm w) hcard_eq
  rw [Finset.coe_univ] at hpd
  exact ⟨hunion, hpd⟩

/-! ### Consequences (1a)–(1d) and Symmetries -/

theorem topSupport_subset_central {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) (t : Fin m) :
    topSupport m hm w t ⊆ centralSet m := by
  have hunion := (claim1_supports_partition hm hw).1
  rw [← hunion]
  exact Finset.subset_biUnion_of_mem (oddSupport m hm w) (Finset.mem_univ (Sum.inl t))

theorem botSupport_subset_central {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) (t : Fin m) :
    botSupport m hm w t ⊆ centralSet m := by
  have hunion := (claim1_supports_partition hm hw).1
  rw [← hunion]
  exact Finset.subset_biUnion_of_mem (oddSupport m hm w) (Finset.mem_univ (Sum.inr t))

/-- **(1a) Tent center bounds:** `2m - t ≤ a_t ≤ N - 2m + t`, and likewise for `b_t`. -/
theorem topCol_bounds {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) (t : Fin m) :
    2 * (m : ℤ) - (t.val : ℤ) ≤ topCol m hm w t ∧
      topCol m hm w t ≤ (N_odd m : ℤ) - 2 * (m : ℤ) + (t.val : ℤ) := by
  have hsub := topSupport_subset_central hm hw t
  have h1 : topCol m hm w t - (tentHeight m t - 1) ∈ topSupport m hm w t := by
    unfold topSupport; rw [Finset.mem_Icc]
    have := tentHeight_pos t; omega
  have h2 : topCol m hm w t + (tentHeight m t - 1) ∈ topSupport m hm w t := by
    unfold topSupport; rw [Finset.mem_Icc]
    have := tentHeight_pos t; omega
  have hc1 := mem_centralSet_iff.mp (hsub h1)
  have hc2 := mem_centralSet_iff.mp (hsub h2)
  have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  unfold tentHeight at hc1 hc2
  omega

theorem botCol_bounds {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) (t : Fin m) :
    2 * (m : ℤ) - (t.val : ℤ) ≤ botCol m hm w t ∧
      botCol m hm w t ≤ (N_odd m : ℤ) - 2 * (m : ℤ) + (t.val : ℤ) := by
  have hsub := botSupport_subset_central hm hw t
  have h1 : botCol m hm w t - (tentHeight m t - 1) ∈ botSupport m hm w t := by
    unfold botSupport; rw [Finset.mem_Icc]
    have := tentHeight_pos t; omega
  have h2 : botCol m hm w t + (tentHeight m t - 1) ∈ botSupport m hm w t := by
    unfold botSupport; rw [Finset.mem_Icc]
    have := tentHeight_pos t; omega
  have hc1 := mem_centralSet_iff.mp (hsub h1)
  have hc2 := mem_centralSet_iff.mp (hsub h2)
  have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  unfold tentHeight at hc1 hc2
  omega

/-- Column `x` is of top type if `x ∈ A_t` for some `t`. -/
def isTopCol (m : ℕ) (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) (x : ℤ) : Prop :=
  ∃ t : Fin m, x ∈ topSupport m hm w t

/-- Column `x` is of bottom type if `x ∈ B_t` for some `t`. -/
def isBotCol (m : ℕ) (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) (x : ℤ) : Prop :=
  ∃ t : Fin m, x ∈ botSupport m hm w t

instance instDecidablePredIsCovered (m : ℕ) (w : Equiv.Perm (Fin (n_odd m))) :
    DecidablePred (isCovered m w) :=
  fun q => decidable_of_iff
    (∃ i : Fin (n_odd m), taxicabDist (plotPoint w i) q ≤ (m : ℤ))
    Iff.rfl

instance instDecidablePredIsTopCol (m : ℕ) (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) :
    DecidablePred (isTopCol m hm w) :=
  fun x => Fintype.decidableExistsFintype (α := Fin m)
    (p := fun t => x ∈ topSupport m hm w t)

instance instDecidablePredIsBotCol (m : ℕ) (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) :
    DecidablePred (isBotCol m hm w) :=
  fun x => Fintype.decidableExistsFintype (α := Fin m)
    (p := fun t => x ∈ botSupport m hm w t)

/-- Overhang `g(x)` for a central column `x ∈ C`. -/
def overhang (m : ℕ) (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) (x : ℤ) : ℤ :=
  ∑ t : Fin m,
    ((if x ∈ topSupport m hm w t then tentHeight m t - |x - topCol m hm w t| else 0) +
     (if x ∈ botSupport m hm w t then tentHeight m t - |x - botCol m hm w t| else 0))

theorem central_mem_top_or_bot {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {x : ℤ} (hx : x ∈ centralSet m) :
    isTopCol m hm w x ∨ isBotCol m hm w x := by
  have hunion := (claim1_supports_partition hm hw).1
  rw [← hunion, Finset.mem_biUnion] at hx
  rcases hx with ⟨s, _, hs⟩
  rcases s with t | t
  · exact Or.inl ⟨t, hs⟩
  · exact Or.inr ⟨t, hs⟩

theorem not_isTopCol_and_isBotCol {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) (x : ℤ) :
    ¬ (isTopCol m hm w x ∧ isBotCol m hm w x) := by
  rintro ⟨⟨t₁, h1⟩, ⟨t₂, h2⟩⟩
  have hpd := (claim1_supports_partition hm hw).2
  have hdisj := hpd (Set.mem_univ (.inl t₁)) (Set.mem_univ (.inr t₂)) (by simp)
  exact Finset.disjoint_left.mp hdisj h1 h2

theorem overhang_eq_of_mem_topSupport {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {t : Fin m} {x : ℤ} (hx : x ∈ topSupport m hm w t) :
    overhang m hm w x = tentHeight m t - |x - topCol m hm w t| := by
  have hpd := (claim1_supports_partition hm hw).2
  unfold overhang
  have hbot0 : ∀ t' : Fin m, x ∉ botSupport m hm w t' := by
    intro t' hmem
    have hdisj := hpd (Set.mem_univ (.inl t)) (Set.mem_univ (.inr t')) (by simp)
    exact Finset.disjoint_left.mp hdisj hx hmem
  have htop0 : ∀ t' : Fin m, t' ≠ t → x ∉ topSupport m hm w t' := by
    intro t' hne hmem
    have hdisj := hpd (Set.mem_univ (.inl t)) (Set.mem_univ (.inl t')) (by simp [hne.symm])
    exact Finset.disjoint_left.mp hdisj hx hmem
  rw [Finset.sum_eq_single t]
  · simp [hx, hbot0 t]
  · intro t' _ hne
    simp [htop0 t' hne, hbot0 t']
  · intro hnot; exact absurd (Finset.mem_univ t) hnot

theorem overhang_eq_of_mem_botSupport {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {t : Fin m} {x : ℤ} (hx : x ∈ botSupport m hm w t) :
    overhang m hm w x = tentHeight m t - |x - botCol m hm w t| := by
  have hpd := (claim1_supports_partition hm hw).2
  unfold overhang
  have htop0 : ∀ t' : Fin m, x ∉ topSupport m hm w t' := by
    intro t' hmem
    have hdisj := hpd (Set.mem_univ (.inr t)) (Set.mem_univ (.inl t')) (by simp)
    exact Finset.disjoint_left.mp hdisj hx hmem
  have hbot0 : ∀ t' : Fin m, t' ≠ t → x ∉ botSupport m hm w t' := by
    intro t' hne hmem
    have hdisj := hpd (Set.mem_univ (.inr t)) (Set.mem_univ (.inr t')) (by simp [hne.symm])
    exact Finset.disjoint_left.mp hdisj hx hmem
  rw [Finset.sum_eq_single t]
  · simp [hx, htop0 t]
  · intro t' _ hne
    simp [htop0 t', hbot0 t' hne]
  · intro hnot; exact absurd (Finset.mem_univ t) hnot

theorem overhang_bounds {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {x : ℤ} (hx : x ∈ centralSet m) :
    1 ≤ overhang m hm w x ∧ overhang m hm w x ≤ (m : ℤ) := by
  rcases central_mem_top_or_bot hm hw hx with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [overhang_eq_of_mem_topSupport hm hw ht]
    have h1 := mem_topSupport_iff.mp ht
    have hnonneg : 0 ≤ |x - topCol m hm w t| := abs_nonneg _
    unfold tentHeight at h1 ⊢
    omega
  · rw [overhang_eq_of_mem_botSupport hm hw ht]
    have h1 := mem_botSupport_iff.mp ht
    have hnonneg : 0 ≤ |x - botCol m hm w t| := abs_nonneg _
    unfold tentHeight at h1 ⊢
    omega

theorem colCover_outside_of_mem_topSupport {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {t : Fin m} {x : ℤ} (hx : x ∈ topSupport m hm w t) :
    (colCover m w x).filter (fun y => (n_odd m : ℤ) + 1 ≤ y) =
      Finset.Icc ((n_odd m : ℤ) + 1) ((n_odd m : ℤ) + overhang m hm w x) ∧
    (colCover m w x).filter (fun y => y ≤ 0) = ∅ := by
  have hpd := (claim1_supports_partition hm hw).2
  have hbot0 : ∀ t' : Fin m, x ∉ botSupport m hm w t' := by
    intro t' hmem
    have hdisj := hpd (Set.mem_univ (.inl t)) (Set.mem_univ (.inr t')) (by simp)
    exact Finset.disjoint_left.mp hdisj hx hmem
  have htop0 : ∀ t' : Fin m, t' ≠ t → x ∉ topSupport m hm w t' := by
    intro t' hne hmem
    have hdisj := hpd (Set.mem_univ (.inl t)) (Set.mem_univ (.inl t')) (by simp [hne.symm])
    exact Finset.disjoint_left.mp hdisj hx hmem
  have hov := overhang_eq_of_mem_topSupport hm hw hx
  constructor
  · ext y
    simp only [Finset.mem_filter, mem_colCover, isCovered, ← mem_sphereColFinset, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨i, hi⟩, hy⟩
      have hne : ((sphereColFinset m (plotPoint w i) x).filter
          (fun y => (n_odd m : ℤ) + 1 ≤ y)).Nonempty :=
        ⟨y, Finset.mem_filter.mpr ⟨hi, hy⟩⟩
      rw [sphereCol_above_box hm w i x] at hne
      split_ifs at hne with hex
      · have hfilt : y ∈ (sphereColFinset m (plotPoint w i) x).filter
            (fun y => (n_odd m : ℤ) + 1 ≤ y) := Finset.mem_filter.mpr ⟨hi, hy⟩
        rw [sphereCol_above_box hm w i x] at hfilt
        split_ifs at hfilt
        rw [Finset.mem_Icc] at hfilt
        have ht_eq : hex.choose = t := by
          by_contra hne_t
          exact htop0 hex.choose hne_t hex.choose_spec.2
        rw [ht_eq] at hfilt
        rwa [← hov] at hfilt
      · exact absurd hne Finset.not_nonempty_empty
    · intro hy
      let i := w.symm (topRowIdx m hm t)
      have hex : ∃ t' : Fin m, w i = topRowIdx m hm t' ∧ x ∈ topSupport m hm w t' :=
        ⟨t, Equiv.apply_symm_apply _ _, hx⟩
      have hfilt : y ∈ (sphereColFinset m (plotPoint w i) x).filter
          (fun y => (n_odd m : ℤ) + 1 ≤ y) := by
        rw [sphereCol_above_box hm w i x]
        split_ifs
        have ht_eq : hex.choose = t := by
          by_contra hne_t
          exact htop0 hex.choose hne_t hex.choose_spec.2
        rw [ht_eq]
        dsimp only
        rw [← hov, Finset.mem_Icc]
        exact hy
      rw [Finset.mem_filter] at hfilt
      exact ⟨⟨i, hfilt.1⟩, hfilt.2⟩
  · ext y
    simp only [Finset.mem_filter, mem_colCover, isCovered, ← mem_sphereColFinset,
      Finset.notMem_empty, iff_false, not_and]
    rintro ⟨i, hi⟩ hy
    have hne : ((sphereColFinset m (plotPoint w i) x).filter (fun y => y ≤ 0)).Nonempty :=
      ⟨y, Finset.mem_filter.mpr ⟨hi, hy⟩⟩
    rw [sphereCol_below_box hm w i x] at hne
    split_ifs at hne with hex
    · exact hbot0 hex.choose hex.choose_spec.2
    · exact absurd hne Finset.not_nonempty_empty

theorem colCover_outside_of_mem_botSupport {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {t : Fin m} {x : ℤ} (hx : x ∈ botSupport m hm w t) :
    (colCover m w x).filter (fun y => y ≤ 0) =
      Finset.Icc (1 - overhang m hm w x) 0 ∧
    (colCover m w x).filter (fun y => (n_odd m : ℤ) + 1 ≤ y) = ∅ := by
  have hpd := (claim1_supports_partition hm hw).2
  have htop0 : ∀ t' : Fin m, x ∉ topSupport m hm w t' := by
    intro t' hmem
    have hdisj := hpd (Set.mem_univ (.inr t)) (Set.mem_univ (.inl t')) (by simp)
    exact Finset.disjoint_left.mp hdisj hx hmem
  have hbot0 : ∀ t' : Fin m, t' ≠ t → x ∉ botSupport m hm w t' := by
    intro t' hne hmem
    have hdisj := hpd (Set.mem_univ (.inr t)) (Set.mem_univ (.inr t')) (by simp [hne.symm])
    exact Finset.disjoint_left.mp hdisj hx hmem
  have hov := overhang_eq_of_mem_botSupport hm hw hx
  constructor
  · ext y
    simp only [Finset.mem_filter, mem_colCover, isCovered, ← mem_sphereColFinset, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨i, hi⟩, hy⟩
      have hne : ((sphereColFinset m (plotPoint w i) x).filter (fun y => y ≤ 0)).Nonempty :=
        ⟨y, Finset.mem_filter.mpr ⟨hi, hy⟩⟩
      rw [sphereCol_below_box hm w i x] at hne
      split_ifs at hne with hex
      · have hfilt : y ∈ (sphereColFinset m (plotPoint w i) x).filter (fun y => y ≤ 0) :=
          Finset.mem_filter.mpr ⟨hi, hy⟩
        rw [sphereCol_below_box hm w i x] at hfilt
        split_ifs at hfilt
        rw [Finset.mem_Icc] at hfilt
        have ht_eq : hex.choose = t := by
          by_contra hne_t
          exact hbot0 hex.choose hne_t hex.choose_spec.2
        rw [ht_eq] at hfilt
        rwa [← hov] at hfilt
      · exact absurd hne Finset.not_nonempty_empty
    · intro hy
      let i := w.symm (botRowIdx m hm t)
      have hex : ∃ t' : Fin m, w i = botRowIdx m hm t' ∧ x ∈ botSupport m hm w t' :=
        ⟨t, Equiv.apply_symm_apply _ _, hx⟩
      have hfilt : y ∈ (sphereColFinset m (plotPoint w i) x).filter (fun y => y ≤ 0) := by
        rw [sphereCol_below_box hm w i x]
        split_ifs
        have ht_eq : hex.choose = t := by
          by_contra hne_t
          exact hbot0 hex.choose hne_t hex.choose_spec.2
        rw [ht_eq]
        dsimp only
        rw [← hov, Finset.mem_Icc]
        exact hy
      rw [Finset.mem_filter] at hfilt
      exact ⟨⟨i, hfilt.1⟩, hfilt.2⟩
  · ext y
    simp only [Finset.mem_filter, mem_colCover, isCovered, ← mem_sphereColFinset,
      Finset.notMem_empty, iff_false, not_and]
    rintro ⟨i, hi⟩ hy
    have hne : ((sphereColFinset m (plotPoint w i) x).filter
        (fun y => (n_odd m : ℤ) + 1 ≤ y)).Nonempty :=
      ⟨y, Finset.mem_filter.mpr ⟨hi, hy⟩⟩
    rw [sphereCol_above_box hm w i x] at hne
    split_ifs at hne with hex
    · exact htop0 hex.choose hex.choose_spec.2
    · exact absurd hne Finset.not_nonempty_empty

/-- Holes of column `x` in `[1, n]`. -/
noncomputable def holesInCol (m : ℕ) (w : Equiv.Perm (Fin (n_odd m))) (x : ℤ) : Finset ℤ :=
  letI := Classical.decPred (isCovered m w)
  (Finset.Icc 1 (n_odd m : ℤ)).filter (fun y => ¬ isCovered m w (x, y))

/-- Holes of row `y` in `[1, n]`. -/
noncomputable def holesInRow (m : ℕ) (w : Equiv.Perm (Fin (n_odd m))) (y : ℤ) : Finset ℤ :=
  letI := Classical.decPred (isCovered m w)
  (Finset.Icc 1 (n_odd m : ℤ)).filter (fun x => ¬ isCovered m w (x, y))

theorem mem_holesInCol {m : ℕ} {w : Equiv.Perm (Fin (n_odd m))} {x y : ℤ} :
    y ∈ holesInCol m w x ↔ 1 ≤ y ∧ y ≤ (n_odd m : ℤ) ∧ ¬ isCovered m w (x, y) := by
  unfold holesInCol
  simp only [Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem mem_holesInRow {m : ℕ} {w : Equiv.Perm (Fin (n_odd m))} {x y : ℤ} :
    x ∈ holesInRow m w y ↔ 1 ≤ x ∧ x ≤ (n_odd m : ℤ) ∧ ¬ isCovered m w (x, y) := by
  unfold holesInRow
  simp only [Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem holesInCol_card_add_colCover_inter {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) (x : ℤ) :
    (holesInCol m w x).card + ((colCover m w x) ∩ Finset.Icc 1 (n_odd m : ℤ)).card =
      n_odd m := by
  have hunion : holesInCol m w x ∪ (colCover m w x ∩ Finset.Icc 1 (n_odd m : ℤ)) =
      Finset.Icc 1 (n_odd m : ℤ) := by
    ext y
    simp only [Finset.mem_union, mem_holesInCol, Finset.mem_inter, Finset.mem_Icc, mem_colCover]
    tauto
  have hdisj : Disjoint (holesInCol m w x) (colCover m w x ∩ Finset.Icc 1 (n_odd m : ℤ)) := by
    refine Finset.disjoint_left.mpr fun y hy1 hy2 => ?_
    rw [mem_holesInCol] at hy1
    rw [Finset.mem_inter, mem_colCover] at hy2
    exact hy1.2.2 hy2.1
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Int.card_Icc]
  omega

/-- **(1b) Central column hole count:** A central column `x ∈ C` has `g(x) - 1` holes. -/
theorem holesInCol_card_central {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {x : ℤ} (hx : x ∈ centralSet m) :
    ((holesInCol m w x).card : ℤ) = overhang m hm w x - 1 := by
  have hsplit : colCover m w x =
      (colCover m w x ∩ Finset.Icc 1 (n_odd m : ℤ)) ∪
        ((colCover m w x).filter (fun y => y ≤ 0) ∪
         (colCover m w x).filter (fun y => (n_odd m : ℤ) + 1 ≤ y)) := by
    ext y
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_filter, Finset.mem_Icc]
    have : (1 ≤ y ∧ y ≤ (n_odd m : ℤ)) ∨ y ≤ 0 ∨ (n_odd m : ℤ) + 1 ≤ y := by omega
    tauto
  have hdisj1 : Disjoint (colCover m w x ∩ Finset.Icc 1 (n_odd m : ℤ))
      ((colCover m w x).filter (fun y => y ≤ 0) ∪
       (colCover m w x).filter (fun y => (n_odd m : ℤ) + 1 ≤ y)) := by
    refine Finset.disjoint_left.mpr fun y h1 h2 => ?_
    simp only [Finset.mem_inter, Finset.mem_Icc] at h1
    simp only [Finset.mem_union, Finset.mem_filter] at h2
    omega
  have hdisj2 : Disjoint ((colCover m w x).filter (fun y => y ≤ 0))
      ((colCover m w x).filter (fun y => (n_odd m : ℤ) + 1 ≤ y)) := by
    refine Finset.disjoint_left.mpr fun y h1 h2 => ?_
    simp only [Finset.mem_filter] at h1 h2
    omega
  have hcard_cov := colCover_card_of_mem_centralSet hm hw hx
  rw [hsplit, Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2] at hcard_cov
  have hov := overhang_bounds hm hw hx
  have hout : (((colCover m w x).filter (fun y => y ≤ 0)).card : ℤ) +
      (((colCover m w x).filter (fun y => (n_odd m : ℤ) + 1 ≤ y)).card : ℤ) =
      overhang m hm w x := by
    rcases central_mem_top_or_bot hm hw hx with ⟨t, ht⟩ | ⟨t, ht⟩
    · obtain ⟨h1, h2⟩ := colCover_outside_of_mem_topSupport hm hw ht
      rw [h1, h2, Finset.card_empty, Int.card_Icc]
      omega
    · obtain ⟨h1, h2⟩ := colCover_outside_of_mem_botSupport hm hw ht
      rw [h1, h2, Finset.card_empty, Int.card_Icc]
      omega
  have hbox := holesInCol_card_add_colCover_inter w x
  have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  zify at hcard_cov hbox
  omega

/-- **(1c) Side columns have no outside coverage:** If `x ∉ C`, every covered cell in column `x`
lies in `[1, n]`. -/
theorem colCover_subset_box_of_not_mem_central {m : ℕ} (hm : 1 ≤ m)
    {w : Equiv.Perm (Fin (n_odd m))} (hw : IsValidOdd m w) {x : ℤ} (hx : x ∉ centralSet m) :
    colCover m w x ⊆ Finset.Icc 1 (n_odd m : ℤ) := by
  intro y hy
  rw [mem_colCover] at hy
  obtain ⟨i, hi⟩ := hy
  rw [← mem_sphereColFinset] at hi
  by_contra hnot
  rw [Finset.mem_Icc] at hnot
  have hcases : (n_odd m : ℤ) + 1 ≤ y ∨ y ≤ 0 := by omega
  rcases hcases with hy_hi | hy_lo
  · have hne : ((sphereColFinset m (plotPoint w i) x).filter
        (fun y => (n_odd m : ℤ) + 1 ≤ y)).Nonempty :=
      ⟨y, Finset.mem_filter.mpr ⟨hi, hy_hi⟩⟩
    rw [sphereCol_above_box hm w i x] at hne
    split_ifs at hne with hex
    · exact hx (topSupport_subset_central hm hw hex.choose hex.choose_spec.2)
    · exact absurd hne Finset.not_nonempty_empty
  · have hne : ((sphereColFinset m (plotPoint w i) x).filter (fun y => y ≤ 0)).Nonempty :=
      ⟨y, Finset.mem_filter.mpr ⟨hi, hy_lo⟩⟩
    rw [sphereCol_below_box hm w i x] at hne
    split_ifs at hne with hex
    · exact hx (botSupport_subset_central hm hw hex.choose hex.choose_spec.2)
    · exact absurd hne Finset.not_nonempty_empty

/-! ### Symmetry Bridges for Supports, Overhang, and Holes -/

private theorem topCol_permComplement {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m)))
    (t : Fin m) :
    topCol m hm (permComplement w) t = botCol m hm w t := by
  unfold topCol botCol permComplement
  have hrev : Fin.rev (topRowIdx m hm t) = botRowIdx m hm t := by
    ext
    rw [Fin.val_rev]
    unfold topRowIdx botRowIdx
    have h2m := two_mul_m_le_n_odd hm
    have ht := t.isLt
    dsimp only
    omega
  change ((w.symm (Fin.rev (topRowIdx m hm t))).val : ℤ) + 1 = _
  rw [hrev]

private theorem botCol_permComplement {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m)))
    (t : Fin m) :
    botCol m hm (permComplement w) t = topCol m hm w t := by
  unfold topCol botCol permComplement
  have hrev : Fin.rev (botRowIdx m hm t) = topRowIdx m hm t := by
    ext
    rw [Fin.val_rev]
    unfold topRowIdx botRowIdx
    have h2m := two_mul_m_le_n_odd hm
    have ht := t.isLt
    dsimp only
    omega
  change ((w.symm (Fin.rev (botRowIdx m hm t))).val : ℤ) + 1 = _
  rw [hrev]

theorem mem_topSupport_permComplement {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m)))
    (t : Fin m) (x : ℤ) :
    x ∈ topSupport m hm (permComplement w) t ↔ x ∈ botSupport m hm w t := by
  rw [mem_topSupport_iff, mem_botSupport_iff, topCol_permComplement]

theorem mem_botSupport_permComplement {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m)))
    (t : Fin m) (x : ℤ) :
    x ∈ botSupport m hm (permComplement w) t ↔ x ∈ topSupport m hm w t := by
  rw [mem_botSupport_iff, mem_topSupport_iff, botCol_permComplement]

theorem isTopCol_permComplement {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) (x : ℤ) :
    isTopCol m hm (permComplement w) x ↔ isBotCol m hm w x := by
  unfold isTopCol isBotCol
  simp only [mem_topSupport_permComplement]

theorem isBotCol_permComplement {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) (x : ℤ) :
    isBotCol m hm (permComplement w) x ↔ isTopCol m hm w x := by
  unfold isTopCol isBotCol
  simp only [mem_botSupport_permComplement]

theorem overhang_permComplement {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) (x : ℤ) :
    overhang m hm (permComplement w) x = overhang m hm w x := by
  unfold overhang
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [mem_topSupport_permComplement, mem_botSupport_permComplement,
    topCol_permComplement, botCol_permComplement]
  ring

private theorem topCol_permReverse {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m)))
    (t : Fin m) :
    topCol m hm (permReverse w) t = (N_odd m : ℤ) - topCol m hm w t := by
  unfold topCol permReverse
  have hsymm : (Fin.revPerm.trans w).symm = w.symm.trans Fin.revPerm := rfl
  rw [hsymm, Equiv.trans_apply]
  change ((Fin.rev (w.symm (topRowIdx m hm t))).val : ℤ) + 1 = _
  rw [fin_rev_add_one]
  have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  rw [hN]

private theorem botCol_permReverse {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m)))
    (t : Fin m) :
    botCol m hm (permReverse w) t = (N_odd m : ℤ) - botCol m hm w t := by
  unfold botCol permReverse
  have hsymm : (Fin.revPerm.trans w).symm = w.symm.trans Fin.revPerm := rfl
  rw [hsymm, Equiv.trans_apply]
  change ((Fin.rev (w.symm (botRowIdx m hm t))).val : ℤ) + 1 = _
  rw [fin_rev_add_one]
  have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  rw [hN]

theorem mem_topSupport_permReverse {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m)))
    (t : Fin m) (x : ℤ) :
    x ∈ topSupport m hm (permReverse w) t ↔ (N_odd m : ℤ) - x ∈ topSupport m hm w t := by
  rw [mem_topSupport_iff, mem_topSupport_iff, topCol_permReverse]
  have heq : x - ((N_odd m : ℤ) - topCol m hm w t) = -(((N_odd m : ℤ) - x) - topCol m hm w t) := by
    ring
  rw [heq, abs_neg]

theorem mem_botSupport_permReverse {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m)))
    (t : Fin m) (x : ℤ) :
    x ∈ botSupport m hm (permReverse w) t ↔ (N_odd m : ℤ) - x ∈ botSupport m hm w t := by
  rw [mem_botSupport_iff, mem_botSupport_iff, botCol_permReverse]
  have heq : x - ((N_odd m : ℤ) - botCol m hm w t) = -(((N_odd m : ℤ) - x) - botCol m hm w t) := by
    ring
  rw [heq, abs_neg]

theorem overhang_permReverse {m : ℕ} (hm : 1 ≤ m) (w : Equiv.Perm (Fin (n_odd m))) (x : ℤ) :
    overhang m hm (permReverse w) x = overhang m hm w ((N_odd m : ℤ) - x) := by
  unfold overhang
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht1 : x - ((N_odd m : ℤ) - topCol m hm w t) = -(((N_odd m : ℤ) - x) - topCol m hm w t) := by
    ring
  have hb1 : x - ((N_odd m : ℤ) - botCol m hm w t) = -(((N_odd m : ℤ) - x) - botCol m hm w t) := by
    ring
  simp only [mem_topSupport_permReverse, mem_botSupport_permReverse,
    topCol_permReverse, botCol_permReverse, ht1, hb1, abs_neg]

/-- **(1d) Corner distance:** Every plot point of a valid `w` is at taxicab distance at least
`2m + 1` from `(0, 0)`, and by symmetry from `(N, 0)`, `(0, N)`, and `(N, N)`. -/
theorem plotPoint_dist_origin {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) (i : Fin (n_odd m)) :
    2 * (m : ℤ) + 1 ≤ taxicabDist (plotPoint w i) (0, 0) := by
  have hbox := plotPoint_mem_box w i
  unfold taxicabDist
  dsimp only
  have hax : |(plotPoint w i).1 - 0| = (plotPoint w i).1 := by
    rw [sub_zero, abs_of_pos]; omega
  have hay : |(plotPoint w i).2 - 0| = (plotPoint w i).2 := by
    rw [sub_zero, abs_of_pos]; omega
  rw [hax, hay]
  suffices h : 2 * (m : ℤ) + 1 ≤ (plotPoint w i).1 + (plotPoint w i).2 by exact h
  -- Case on whether y ≤ m, x ≤ m, or both ≥ m + 1
  by_cases hy : (plotPoint w i).2 ≤ (m : ℤ)
  · unfold plotPoint at hy
    let t : Fin m := ⟨(w i).val, by omega⟩
    have hbot : (plotPoint w i).1 = botCol m hm w t := by
      unfold botCol plotPoint
      have hwi : w i = botRowIdx m hm t := by ext; rfl
      have : i = w.symm (botRowIdx m hm t) := by
        apply w.injective; rw [hwi, Equiv.apply_symm_apply]
      rw [this]
    have hbd := (botCol_bounds hm hw t).1
    have ht_val : (t.val : ℤ) = ((w i).val : ℤ) := rfl
    rw [← hbot, ht_val] at hbd
    unfold plotPoint at hbd ⊢
    dsimp only at hbd ⊢
    omega
  · by_cases hx : (plotPoint w i).1 ≤ (m : ℤ)
    · -- Apply the y ≤ m case to permInverse w at w i!
      have hinv_valid : IsValidOdd m (permInverse w) := isValidPerm_permInverse hw
      have hpt_inv : plotPoint (permInverse w) (w i) = ptTranspose (plotPoint w i) :=
        plotPoint_permInverse w i
      have hy' : (plotPoint (permInverse w) (w i)).2 ≤ (m : ℤ) := by
        rw [hpt_inv]; exact hx
      unfold plotPoint at hy'
      let t : Fin m := ⟨((permInverse w) (w i)).val, by omega⟩
      have hbot : (plotPoint (permInverse w) (w i)).1 = botCol m hm (permInverse w) t := by
        unfold botCol plotPoint
        have hwi : (permInverse w) (w i) = botRowIdx m hm t := by ext; rfl
        have : w i = (permInverse w).symm (botRowIdx m hm t) := by
          apply (permInverse w).injective; rw [hwi, Equiv.apply_symm_apply]
        rw [this]
      have hbd := (botCol_bounds hm hinv_valid t).1
      have hinv_eq : (permInverse w) (w i) = i := w.symm_apply_apply i
      have ht_val : (t.val : ℤ) = (i.val : ℤ) := by dsimp [t]; rw [hinv_eq]
      rw [← hbot, hpt_inv, ht_val] at hbd
      unfold ptTranspose at hbd
      unfold plotPoint at hbd ⊢
      dsimp only at hbd ⊢
      omega
    · omega

theorem plotPoint_dist_all_corners {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) (i : Fin (n_odd m)) :
    2 * (m : ℤ) + 1 ≤ taxicabDist (plotPoint w i) (0, 0) ∧
    2 * (m : ℤ) + 1 ≤ taxicabDist (plotPoint w i) ((N_odd m : ℤ), 0) ∧
    2 * (m : ℤ) + 1 ≤ taxicabDist (plotPoint w i) (0, (N_odd m : ℤ)) ∧
    2 * (m : ℤ) + 1 ≤ taxicabDist (plotPoint w i) ((N_odd m : ℤ), (N_odd m : ℤ)) := by
  have hN : ((n_odd m : ℤ) + 1) = (N_odd m : ℤ) := by exact_mod_cast n_odd_add_one m
  refine ⟨plotPoint_dist_origin hm hw i, ?_, ?_, ?_⟩
  · have h := plotPoint_dist_origin hm (isValidPerm_permReverse hw) (Fin.rev i)
    have hpt : plotPoint (permReverse w) (Fin.rev i) = ptFlipX (N_odd m : ℤ) (plotPoint w i) := by
      rw [← hN]; exact plotPoint_permReverse w i
    rw [hpt, taxicabDist_ptFlipX_left] at h
    simpa [ptFlipX] using h
  · have h := plotPoint_dist_origin hm (isValidPerm_permComplement hw) i
    have hpt : plotPoint (permComplement w) i = ptFlipY (N_odd m : ℤ) (plotPoint w i) := by
      rw [← hN]; exact plotPoint_permComplement w i
    rw [hpt, taxicabDist_ptFlipY_left] at h
    simpa [ptFlipY] using h
  · have h := plotPoint_dist_origin hm (isValidPerm_permReverse (isValidPerm_permComplement hw))
      (Fin.rev i)
    have hpt : plotPoint (permReverse (permComplement w)) (Fin.rev i) =
        ptFlipX (N_odd m : ℤ) (ptFlipY (N_odd m : ℤ) (plotPoint w i)) := by
      rw [← hN, plotPoint_permReverse, plotPoint_permComplement]
    rw [hpt, taxicabDist_ptFlipX_left, taxicabDist_ptFlipY_left] at h
    simpa [ptFlipX, ptFlipY] using h

theorem corner_sphere_isHole {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {q corner : ℤ × ℤ}
    (hcorner : corner = (0, 0) ∨ corner = ((N_odd m : ℤ), 0) ∨
      corner = (0, (N_odd m : ℤ)) ∨ corner = ((N_odd m : ℤ), (N_odd m : ℤ)))
    (hq1 : 1 ≤ q.1) (hq2 : q.1 ≤ (n_odd m : ℤ))
    (hq3 : 1 ≤ q.2) (hq4 : q.2 ≤ (n_odd m : ℤ))
    (hsph : q ∈ leeSphere m corner) :
    isHole m w q := by
  refine ⟨hq1, hq2, hq3, hq4, ?_⟩
  rintro ⟨i, hi⟩
  have hcd := plotPoint_dist_all_corners hm hw i
  have hdist : 2 * (m : ℤ) + 1 ≤ taxicabDist (plotPoint w i) corner := by
    rcases hcorner with rfl | rfl | rfl | rfl
    · exact hcd.1
    · exact hcd.2.1
    · exact hcd.2.2.1
    · exact hcd.2.2.2
  have hdisj := (sphere_disjoint_iff m (plotPoint w i) corner).mpr hdist
  exact Set.disjoint_left.mp hdisj hi hsph

/-! ## Section 3: Step 2 — Side Columns and Side Rows (Claim 2) -/

private theorem sum_range_two_mul_add_one (s : ℕ) :
    ∑ k ∈ Finset.range s, (2 * k + 1) = s ^ 2 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- **Claim 2 (left side columns):** For `1 ≤ s ≤ m`, column `x = m + 1 - s` has `s^2 - 1` holes. -/
theorem claim2_left_side_col_holes {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {s : ℕ} (hs1 : 1 ≤ s) (hsm : s ≤ m) :
    (holesInCol m w ((m : ℤ) + 1 - (s : ℤ))).card = s ^ 2 - 1 := by
  let x : ℤ := (m : ℤ) + 1 - (s : ℤ)
  have hx_not_C : x ∉ centralSet m := by
    rw [mem_centralSet_iff]; dsimp [x]; omega
  have hsub := colCover_subset_box_of_not_mem_central hm hw hx_not_C
  have hinter : colCover m w x ∩ Finset.Icc 1 (n_odd m : ℤ) = colCover m w x :=
    Finset.inter_eq_left.mpr hsub
  have hbox := holesInCol_card_add_colCover_inter w x
  rw [hinter] at hbox
  have hcov_sum := colCover_card_eq_sum hw x
  have h2m := two_mul_m_le_n_odd hm
  have hsplit : (colCover m w x).card =
      ∑ c ∈ Finset.Icc 1 (x + (m : ℤ)), (2 * (m - (x - c).natAbs) + 1) := by
    rw [hcov_sum, ← Finset.sum_subset (Finset.filter_subset
        (fun i : Fin (n_odd m) => (x - ((i.val : ℤ) + 1)).natAbs ≤ m) Finset.univ)]
    · refine Finset.sum_bij (fun i _ => ((i.val : ℤ) + 1)) ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_filter] at hi
        rw [Finset.mem_Icc]
        dsimp [x] at hi ⊢
        omega
      · intro i₁ _ i₂ _ h
        exact Fin.ext (by omega)
      · intro c hc
        rw [Finset.mem_Icc] at hc
        have hc_n : c ≤ (n_odd m : ℤ) := by dsimp [x] at hc; omega
        refine ⟨⟨(c - 1).toNat, by omega⟩, ?_, by dsimp only; omega⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        dsimp only
        have heq : (x - (((c - 1).toNat : ℤ) + 1)) = x - c := by omega
        rw [heq]
        dsimp [x] at hc
        omega
      · intro i hi
        rw [Finset.mem_filter] at hi
        rw [card_sphereColFinset]
        unfold plotPoint
        simp [hi.2]
    · intro i _ hnot
      rw [Finset.mem_filter, not_and] at hnot
      have hgt : ¬ (x - ((i.val : ℤ) + 1)).natAbs ≤ m := fun h => hnot (Finset.mem_univ _) h
      rw [card_sphereColFinset]
      unfold plotPoint
      simp [hgt]
  have htail :
      ∑ c ∈ Finset.Icc (x - (m : ℤ)) 0, (2 * (m - (x - c).natAbs) + 1) = s ^ 2 := by
    have hbij :
        ∑ c ∈ Finset.Icc (x - (m : ℤ)) 0, (2 * (m - (x - c).natAbs) + 1) =
          ∑ k ∈ Finset.range s, (2 * k + 1) := by
      refine Finset.sum_bij (fun c _ => (c - (x - (m : ℤ))).toNat) ?_ ?_ ?_ ?_
      · intro c hc
        rw [Finset.mem_Icc] at hc
        rw [Finset.mem_range]
        dsimp [x] at hc ⊢
        omega
      · intro c₁ hc₁ c₂ hc₂ h
        rw [Finset.mem_Icc] at hc₁ hc₂
        omega
      · intro k hk
        rw [Finset.mem_range] at hk
        refine ⟨x - (m : ℤ) + (k : ℤ), ?_, by omega⟩
        rw [Finset.mem_Icc]
        dsimp [x]
        omega
      · intro c hc
        rw [Finset.mem_Icc] at hc
        have heq : m - (x - c).natAbs = (c - (x - (m : ℤ))).toNat := by
          dsimp [x] at hc ⊢
          omega
        rw [heq]
    rw [hbij, sum_range_two_mul_add_one]
  have hfull :
      ∑ c ∈ Finset.Icc (x - (m : ℤ)) (x + (m : ℤ)), (2 * (m - (x - c).natAbs) + 1) = N_odd m := by
    have hbij :
        ∑ c ∈ Finset.Icc (x - (m : ℤ)) (x + (m : ℤ)), (2 * (m - (x - c).natAbs) + 1) =
          ∑ j ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), (2 * (m - j.natAbs) + 1) := by
      refine Finset.sum_bij (fun c _ => x - c) ?_ ?_ ?_ ?_
      · intro c hc; rw [Finset.mem_Icc] at hc ⊢; omega
      · intro c₁ _ c₂ _ h; omega
      · intro j hj; rw [Finset.mem_Icc] at hj
        refine ⟨x - j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by ring⟩
      · intro c _; rfl
    rw [hbij, sum_chord_Icc]
    rfl
  have hunion_Icc : Finset.Icc (x - (m : ℤ)) (x + (m : ℤ)) =
      Finset.Icc (x - (m : ℤ)) 0 ∪ Finset.Icc 1 (x + (m : ℤ)) := by
    ext c
    simp only [Finset.mem_union, Finset.mem_Icc]
    dsimp [x]
    omega
  have hdisj_Icc : Disjoint (Finset.Icc (x - (m : ℤ)) 0) (Finset.Icc 1 (x + (m : ℤ))) := by
    refine Finset.disjoint_left.mpr fun c h1 h2 => ?_
    rw [Finset.mem_Icc] at h1 h2
    omega
  rw [hunion_Icc, Finset.sum_union hdisj_Icc, htail, ← hsplit] at hfull
  have hN : N_odd m = n_odd m + 1 := (n_odd_add_one m).symm
  have hs2 : 1 ≤ s ^ 2 := by have := hs1; nlinarith
  have hplus : (holesInCol m w x).card + 1 = s ^ 2 := by omega
  exact Nat.eq_sub_of_add_eq hplus

theorem holesInCol_card_permReverse {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) (x : ℤ) :
    (holesInCol m (permReverse w) x).card = (holesInCol m w ((N_odd m : ℤ) - x)).card := by
  refine Finset.card_bij (fun y _ => y) ?_ ?_ ?_
  · intro y hy
    rw [mem_holesInCol] at hy ⊢
    refine ⟨hy.1, hy.2.1, ?_⟩
    rw [isCovered_permReverse] at hy
    exact hy.2.2
  · intro _ _ _ _ h; exact h
  · intro y hy
    rw [mem_holesInCol] at hy
    refine ⟨y, mem_holesInCol.mpr ⟨hy.1, hy.2.1, ?_⟩, rfl⟩
    rw [isCovered_permReverse]
    exact hy.2.2

theorem holesInCol_card_permComplement {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) (x : ℤ) :
    (holesInCol m (permComplement w) x).card = (holesInCol m w x).card := by
  refine Finset.card_bij (fun y _ => (N_odd m : ℤ) - y) ?_ ?_ ?_
  · intro y hy
    rw [mem_holesInCol] at hy ⊢
    have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
    rw [isCovered_permComplement] at hy
    exact ⟨by omega, by omega, hy.2.2⟩
  · intro _ _ _ _ h; omega
  · intro y hy
    rw [mem_holesInCol] at hy
    have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
    refine ⟨(N_odd m : ℤ) - y, mem_holesInCol.mpr ⟨by omega, by omega, ?_⟩, by ring⟩
    rw [isCovered_permComplement]
    simpa [ptFlipY] using hy.2.2

theorem holesInRow_card_eq_holesInCol_permInverse {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) (y : ℤ) :
    (holesInRow m w y).card = (holesInCol m (permInverse w) y).card := by
  refine Finset.card_bij (fun x _ => x) ?_ ?_ ?_
  · intro x hx
    rw [mem_holesInRow] at hx
    rw [mem_holesInCol, isCovered_permInverse]
    exact hx
  · intro _ _ _ _ h; exact h
  · intro x hx
    rw [mem_holesInCol, isCovered_permInverse] at hx
    exact ⟨x, mem_holesInRow.mpr hx, rfl⟩

/-- **Claim 2 (all 4 sides):** Side columns and side rows at offset `s` (`1 ≤ s ≤ m`) each
contain `s^2 - 1` holes; in particular columns/rows `m` and `N - m` contain zero holes. -/
theorem claim2_right_side_col_holes {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {s : ℕ} (hs1 : 1 ≤ s) (hsm : s ≤ m) :
    (holesInCol m w ((N_odd m : ℤ) - ((m : ℤ) + 1 - (s : ℤ)))).card = s ^ 2 - 1 := by
  rw [← holesInCol_card_permReverse w ((m : ℤ) + 1 - (s : ℤ))]
  exact claim2_left_side_col_holes hm (isValidPerm_permReverse hw) hs1 hsm

theorem claim2_bot_side_row_holes {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {s : ℕ} (hs1 : 1 ≤ s) (hsm : s ≤ m) :
    (holesInRow m w ((m : ℤ) + 1 - (s : ℤ))).card = s ^ 2 - 1 := by
  rw [holesInRow_card_eq_holesInCol_permInverse]
  exact claim2_left_side_col_holes hm (isValidPerm_permInverse hw) hs1 hsm

theorem claim2_top_side_row_holes {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {s : ℕ} (hs1 : 1 ≤ s) (hsm : s ≤ m) :
    (holesInRow m w ((N_odd m : ℤ) - ((m : ℤ) + 1 - (s : ℤ)))).card = s ^ 2 - 1 := by
  rw [holesInRow_card_eq_holesInCol_permInverse]
  exact claim2_right_side_col_holes hm (isValidPerm_permInverse hw) hs1 hsm

theorem col_m_no_holes {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) :
    ∀ y : ℤ, 1 ≤ y → y ≤ (n_odd m : ℤ) → isCovered m w ((m : ℤ), y) := by
  intro y hy1 hyn
  have h0 := claim2_left_side_col_holes hm hw (s := 1) le_rfl hm
  simp only [Nat.cast_one, add_sub_cancel_right, one_pow, Nat.sub_self, Finset.card_eq_zero] at h0
  by_contra hnc
  have hmem : y ∈ holesInCol m w (m : ℤ) := mem_holesInCol.mpr ⟨hy1, hyn, hnc⟩
  rw [h0] at hmem
  exact Finset.notMem_empty y hmem

theorem col_N_sub_m_no_holes {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) :
    ∀ y : ℤ, 1 ≤ y → y ≤ (n_odd m : ℤ) → isCovered m w ((N_odd m : ℤ) - (m : ℤ), y) := by
  intro y hy1 hyn
  have h0 := claim2_right_side_col_holes hm hw (s := 1) le_rfl hm
  simp only [Nat.cast_one, add_sub_cancel_right, one_pow, Nat.sub_self, Finset.card_eq_zero] at h0
  by_contra hnc
  have hmem : y ∈ holesInCol m w ((N_odd m : ℤ) - (m : ℤ)) := mem_holesInCol.mpr ⟨hy1, hyn, hnc⟩
  rw [h0] at hmem
  exact Finset.notMem_empty y hmem

/-! ## Section 4: Step 3 — Corner Points and Corner Squares (Claim 3 & (3a)) -/

private theorem cell_m_one_covered_alt {m : ℕ} (hm : 1 ≤ m)
    {w : Equiv.Perm (Fin (n_odd m))} (hw : IsValidOdd m w) :
    ((m : ℤ), (m : ℤ) + 1) ∈ plotSet w ∨ isBotCol m hm w ((m : ℤ) + 1) := by
  have hcov := col_m_no_holes hm hw 1 (by omega) (by exact_mod_cast n_odd_pos hm)
  obtain ⟨i, hi⟩ := hcov
  change taxicabDist (plotPoint w i) ((m : ℤ), 1) ≤ (m : ℤ) at hi
  unfold taxicabDist plotPoint at hi
  dsimp only at hi
  have hwi_lt := (w i).isLt
  have hi_lt := i.isLt
  by_cases hy : (m : ℤ) + 1 ≤ ((w i).val : ℤ) + 1
  · left
    refine ⟨i, ?_⟩
    have h1 : |((w i).val : ℤ) + 1 - 1| = ((w i).val : ℤ) := by
      rw [abs_of_nonneg] <;> omega
    have hnonneg : 0 ≤ |((i.val : ℤ) + 1) - (m : ℤ)| := abs_nonneg _
    have hyeq : ((w i).val : ℤ) + 1 = (m : ℤ) + 1 := by omega
    have hxeq : ((i.val : ℤ) + 1) = (m : ℤ) := by
      have hab : |((i.val : ℤ) + 1) - (m : ℤ)| = 0 := by omega
      have := abs_eq_zero.mp hab
      omega
    unfold plotPoint
    exact Prod.ext hxeq hyeq
  · right
    let t : Fin m := ⟨(w i).val, by omega⟩
    have hwi : w i = botRowIdx m hm t := by ext; rfl
    have hbot : botCol m hm w t = (i.val : ℤ) + 1 := by
      unfold botCol
      have : w.symm (botRowIdx m hm t) = i := by
        rw [← hwi, Equiv.symm_apply_apply]
      rw [this]
    have hbd := (botCol_bounds hm hw t).1
    have haby : |((w i).val : ℤ) + 1 - 1| = (t.val : ℤ) := by
      dsimp [t]; rw [abs_of_nonneg] <;> omega
    have hceq : (i.val : ℤ) + 1 = 2 * (m : ℤ) - (t.val : ℤ) := by
      rcases abs_le.mp (by omega : |((i.val : ℤ) + 1) - (m : ℤ)| ≤ (m : ℤ) - (t.val : ℤ)) with
        ⟨_, _⟩
      omega
    refine ⟨t, mem_botSupport_iff.mpr ?_⟩
    rw [hbot, hceq]
    unfold tentHeight
    rw [abs_le]
    omega

/-- **Claim 3 (column `m`):** Either `(m, m + 1)` or `(m, N - m - 1)` belongs to `plotSet w`
(and not both). -/
theorem claim3_col_m {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) :
    ((m : ℤ), (m : ℤ) + 1) ∈ plotSet w ∨ ((m : ℤ), (N_odd m : ℤ) - (m : ℤ) - 1) ∈ plotSet w := by
  rcases cell_m_one_covered_alt hm hw with h1 | hbot
  · exact Or.inl h1
  · rcases cell_m_one_covered_alt hm (isValidPerm_permComplement hw) with h2 | hbot'
    · right
      obtain ⟨i, hi⟩ := h2
      refine ⟨i, ?_⟩
      have hN : ((n_odd m : ℤ) + 1) = (N_odd m : ℤ) := by exact_mod_cast n_odd_add_one m
      have hpt := plotPoint_permComplement w i
      rw [hN, hi] at hpt
      unfold ptFlipY at hpt
      have hfst := (Prod.mk.inj hpt).1
      have hsnd := (Prod.mk.inj hpt).2
      ext <;> dsimp only <;> omega
    · rw [isBotCol_permComplement] at hbot'
      exact absurd ⟨hbot', hbot⟩ (not_isTopCol_and_isBotCol hm hw ((m : ℤ) + 1))

private theorem plotSet_permReverse_iff {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) (p : ℤ × ℤ) :
    p ∈ plotSet (permReverse w) ↔ ptFlipX (N_odd m : ℤ) p ∈ plotSet w := by
  have hN : ((n_odd m : ℤ) + 1) = (N_odd m : ℤ) := by exact_mod_cast n_odd_add_one m
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.rev i, ?_⟩
    have h := plotPoint_permReverse w (Fin.rev i)
    rw [hN, Fin.rev_rev] at h
    rw [h]
    unfold ptFlipX
    exact Prod.ext (by dsimp only; ring) rfl
  · rintro ⟨i, hi⟩
    refine ⟨Fin.rev i, ?_⟩
    have h := plotPoint_permReverse w i
    rw [hN, hi] at h
    unfold ptFlipX at h
    simp only [sub_sub_cancel] at h
    exact h

private theorem plotSet_permInverse_iff {m : ℕ} (w : Equiv.Perm (Fin (n_odd m))) (p : ℤ × ℤ) :
    p ∈ plotSet (permInverse w) ↔ ptTranspose p ∈ plotSet w := by
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨w.symm i, ?_⟩
    have h := plotPoint_permInverse w (w.symm i)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
    unfold ptTranspose; ext <;> rfl
  · rintro ⟨i, hi⟩
    refine ⟨w i, ?_⟩
    have h := plotPoint_permInverse w i
    rw [hi] at h
    exact h

private noncomputable def ind (P : Prop) : ℕ := by
  classical exact if P then 1 else 0

private theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  unfold ind; split_ifs <;> omega

private theorem ind_or_eq_one {P Q : Prop} (hor : P ∨ Q) (hne : ¬ (P ∧ Q)) :
    ind P + ind Q = 1 := by
  unfold ind
  split_ifs with h1 h2 h2
  · exact absurd ⟨h1, h2⟩ hne
  · rfl
  · rfl
  · exact absurd hor (not_or.mpr ⟨h1, h2⟩)

private theorem ind_at_most_one {m : ℕ} {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {p q : ℤ × ℤ} (hpq : p ≠ q)
    (hdist : taxicabDist p q < (d_odd m : ℤ)) :
    ind (p ∈ plotSet w) + ind (q ∈ plotSet w) ≤ 1 := by
  unfold ind
  split_ifs with hp hq
  · exfalso
    have hv := (isValidPerm_iff_plotSet w).mp hw p hp q hq hpq
    omega
  · omega
  · omega
  · omega

/-- **Claim 3 (all 4 corners):** At each of the four corners, exactly one of the two corner-adjacent
cells belongs to `plotSet w`. -/
theorem claim3_corners {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) :
    (((m : ℤ), (m : ℤ) + 1) ∈ plotSet w ↔ ((m : ℤ) + 1, (m : ℤ)) ∉ plotSet w) ∧
    (((m : ℤ), (m : ℤ) + 1) ∈ plotSet w ∨ ((m : ℤ) + 1, (m : ℤ)) ∈ plotSet w) ∧
    (((N_odd m : ℤ) - (m : ℤ), (m : ℤ) + 1) ∈ plotSet w ↔
      ((N_odd m : ℤ) - (m : ℤ) - 1, (m : ℤ)) ∉ plotSet w) ∧
    (((N_odd m : ℤ) - (m : ℤ), (m : ℤ) + 1) ∈ plotSet w ∨
      ((N_odd m : ℤ) - (m : ℤ) - 1, (m : ℤ)) ∈ plotSet w) ∧
    (((m : ℤ), (N_odd m : ℤ) - (m : ℤ) - 1) ∈ plotSet w ↔
      ((m : ℤ) + 1, (N_odd m : ℤ) - (m : ℤ)) ∉ plotSet w) ∧
    (((m : ℤ), (N_odd m : ℤ) - (m : ℤ) - 1) ∈ plotSet w ∨
      ((m : ℤ) + 1, (N_odd m : ℤ) - (m : ℤ)) ∈ plotSet w) ∧
    (((N_odd m : ℤ) - (m : ℤ), (N_odd m : ℤ) - (m : ℤ) - 1) ∈ plotSet w ↔
      ((N_odd m : ℤ) - (m : ℤ) - 1, (N_odd m : ℤ) - (m : ℤ)) ∉ plotSet w) ∧
    (((N_odd m : ℤ) - (m : ℤ), (N_odd m : ℤ) - (m : ℤ) - 1) ∈ plotSet w ∨
      ((N_odd m : ℤ) - (m : ℤ) - 1, (N_odd m : ℤ) - (m : ℤ)) ∈ plotSet w) := by
  have hN_gt : (m : ℤ) + 1 < (N_odd m : ℤ) - (m : ℤ) - 1 := by
    have hmZ : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
    have : (N_odd m : ℤ) = 2 * (m : ℤ) ^ 2 + 2 * (m : ℤ) + 1 := by unfold N_odd; push_cast; ring
    nlinarith
  have hcol1 := claim3_col_m hm hw
  have hcol2 : ((N_odd m : ℤ) - (m : ℤ), (m : ℤ) + 1) ∈ plotSet w ∨
      ((N_odd m : ℤ) - (m : ℤ), (N_odd m : ℤ) - (m : ℤ) - 1) ∈ plotSet w := by
    have h := claim3_col_m hm (isValidPerm_permReverse hw)
    rw [plotSet_permReverse_iff, plotSet_permReverse_iff] at h
    simpa [ptFlipX] using h
  have hrow1 : ((m : ℤ) + 1, (m : ℤ)) ∈ plotSet w ∨
      ((N_odd m : ℤ) - (m : ℤ) - 1, (m : ℤ)) ∈ plotSet w := by
    have h := claim3_col_m hm (isValidPerm_permInverse hw)
    rw [plotSet_permInverse_iff, plotSet_permInverse_iff] at h
    simpa [ptTranspose] using h
  have hrow2 : ((m : ℤ) + 1, (N_odd m : ℤ) - (m : ℤ)) ∈ plotSet w ∨
      ((N_odd m : ℤ) - (m : ℤ) - 1, (N_odd m : ℤ) - (m : ℤ)) ∈ plotSet w := by
    have h := claim3_col_m hm (isValidPerm_permReverse (isValidPerm_permInverse hw))
    rw [plotSet_permReverse_iff, plotSet_permReverse_iff,
      plotSet_permInverse_iff, plotSet_permInverse_iff] at h
    simpa [ptFlipX, ptTranspose] using h
  have hsame_x : ∀ x y₁ y₂ : ℤ, y₁ ≠ y₂ → ¬ ((x, y₁) ∈ plotSet w ∧ (x, y₂) ∈ plotSet w) := by
    rintro x y₁ y₂ hne ⟨⟨i₁, h1⟩, ⟨i₂, h2⟩⟩
    have hi : i₁ = i₂ := Fin.ext (by
      have hx1 := congrArg Prod.fst h1
      have hx2 := congrArg Prod.fst h2
      unfold plotPoint at hx1 hx2; dsimp only at hx1 hx2; omega)
    subst hi
    exact hne (Prod.mk.inj (h1.symm.trans h2)).2
  have hsame_y : ∀ x₁ x₂ y : ℤ, x₁ ≠ x₂ → ¬ ((x₁, y) ∈ plotSet w ∧ (x₂, y) ∈ plotSet w) := by
    rintro x₁ x₂ y hne ⟨⟨i₁, h1⟩, ⟨i₂, h2⟩⟩
    have hwi : w i₁ = w i₂ := Fin.ext (by
      have hy1 := congrArg Prod.snd h1
      have hy2 := congrArg Prod.snd h2
      unfold plotPoint at hy1 hy2; dsimp only at hy1 hy2; omega)
    have hi := w.injective hwi
    subst hi
    exact hne (Prod.mk.inj (h1.symm.trans h2)).1
  have e1 := ind_or_eq_one hcol1 (hsame_x _ _ _ (by omega))
  have e2 := ind_or_eq_one hcol2 (hsame_x _ _ _ (by omega))
  have e3 := ind_or_eq_one hrow1 (hsame_y _ _ _ (by omega))
  have e4 := ind_or_eq_one hrow2 (hsame_y _ _ _ (by omega))
  have hd_lt : (2 : ℤ) < (d_odd m : ℤ) := by unfold d_odd; omega
  have c1 := ind_at_most_one hw (p := ((m : ℤ), (m : ℤ) + 1)) (q := ((m : ℤ) + 1, (m : ℤ)))
    (by intro h; have := (Prod.mk.inj h).1; omega)
    (by unfold taxicabDist; simp; omega)
  have c2 := ind_at_most_one hw (p := ((N_odd m : ℤ) - (m : ℤ), (m : ℤ) + 1))
    (q := ((N_odd m : ℤ) - (m : ℤ) - 1, (m : ℤ)))
    (by intro h; have := (Prod.mk.inj h).1; omega)
    (by unfold taxicabDist; simp; omega)
  have c3 := ind_at_most_one hw (p := ((m : ℤ), (N_odd m : ℤ) - (m : ℤ) - 1))
    (q := ((m : ℤ) + 1, (N_odd m : ℤ) - (m : ℤ)))
    (by intro h; have := (Prod.mk.inj h).1; omega)
    (by unfold taxicabDist; simp; omega)
  have c4 := ind_at_most_one hw (p := ((N_odd m : ℤ) - (m : ℤ), (N_odd m : ℤ) - (m : ℤ) - 1))
    (q := ((N_odd m : ℤ) - (m : ℤ) - 1, (N_odd m : ℤ) - (m : ℤ)))
    (by intro h; have := (Prod.mk.inj h).1; omega)
    (by unfold taxicabDist; simp; omega)
  have s1 : ind (((m : ℤ), (m : ℤ) + 1) ∈ plotSet w) +
      ind (((m : ℤ) + 1, (m : ℤ)) ∈ plotSet w) = 1 := by omega
  have s2 : ind (((N_odd m : ℤ) - (m : ℤ), (m : ℤ) + 1) ∈ plotSet w) +
      ind (((N_odd m : ℤ) - (m : ℤ) - 1, (m : ℤ)) ∈ plotSet w) = 1 := by omega
  have s3 : ind (((m : ℤ), (N_odd m : ℤ) - (m : ℤ) - 1) ∈ plotSet w) +
      ind (((m : ℤ) + 1, (N_odd m : ℤ) - (m : ℤ)) ∈ plotSet w) = 1 := by omega
  have s4 : ind (((N_odd m : ℤ) - (m : ℤ), (N_odd m : ℤ) - (m : ℤ) - 1) ∈ plotSet w) +
      ind (((N_odd m : ℤ) - (m : ℤ) - 1, (N_odd m : ℤ) - (m : ℤ)) ∈ plotSet w) = 1 := by omega
  have of_ind : ∀ {P Q : Prop}, ind P + ind Q = 1 → (P ↔ ¬ Q) ∧ (P ∨ Q) := by
    intro P Q h
    unfold ind at h
    split_ifs at h with hP hQ hQ
    · omega
    · exact ⟨by tauto, Or.inl hP⟩
    · exact ⟨by tauto, Or.inr hQ⟩
    · omega
  exact ⟨(of_ind s1).1, (of_ind s1).2, (of_ind s2).1, (of_ind s2).2,
    (of_ind s3).1, (of_ind s3).2, (of_ind s4).1, (of_ind s4).2⟩

/-- **(3a) Corner square `[1, m]^2`:** A cell `(x, y) ∈ [1, m]^2` is a hole iff `x + y ≤ m`. -/
theorem claim3a_corner_square_00 {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {x y : ℤ} (hx1 : 1 ≤ x) (hxm : x ≤ (m : ℤ))
    (hy1 : 1 ≤ y) (hym : y ≤ (m : ℤ)) :
    isHole m w (x, y) ↔ x + y ≤ (m : ℤ) := by
  have h2m := two_mul_m_le_n_odd hm
  have hx_n : x ≤ (n_odd m : ℤ) := by omega
  have hy_n : y ≤ (n_odd m : ℤ) := by omega
  constructor
  · intro hhole
    by_contra hgt
    have hge : (m : ℤ) + 1 ≤ x + y := by omega
    have hcov : isCovered m w (x, y) := by
      rcases (claim3_corners hm hw).2.1 with ⟨i, hi⟩ | ⟨i, hi⟩
      · refine ⟨i, ?_⟩
        change taxicabDist (plotPoint w i) (x, y) ≤ (m : ℤ)
        rw [hi]
        unfold taxicabDist
        dsimp only
        rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
        omega
      · refine ⟨i, ?_⟩
        change taxicabDist (plotPoint w i) (x, y) ≤ (m : ℤ)
        rw [hi]
        unfold taxicabDist
        dsimp only
        rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
        omega
    exact hhole.2.2.2.2 hcov
  · intro hle
    apply corner_sphere_isHole hm hw (Or.inl rfl) hx1 hx_n hy1 hy_n
    change taxicabDist (0, 0) (x, y) ≤ (m : ℤ)
    unfold taxicabDist
    dsimp only
    rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]
    omega

private theorem corner_row_holes_00 {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {y : ℤ} (hy1 : 1 ≤ y) (hym : y ≤ (m : ℤ)) :
    ((Finset.Icc 1 (m : ℤ)).filter (fun x => ¬ isCovered m w (x, y))).card = m - y.toNat := by
  have h2m := two_mul_m_le_n_odd hm
  have heq : (Finset.Icc 1 (m : ℤ)).filter (fun x => ¬ isCovered m w (x, y)) =
      Finset.Icc 1 ((m : ℤ) - y) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hx1, hxm⟩, hnc⟩
      have hhole : isHole m w (x, y) := ⟨hx1, by omega, hy1, by omega, hnc⟩
      have hle := (claim3a_corner_square_00 hm hw hx1 hxm hy1 hym).mp hhole
      exact ⟨hx1, by omega⟩
    · intro ⟨hx1, hxm⟩
      have hhole := (claim3a_corner_square_00 hm hw hx1 (by omega) hy1 hym).mpr (by omega)
      exact ⟨⟨hx1, by omega⟩, hhole.2.2.2.2⟩
  rw [heq, Int.card_Icc]
  omega

private theorem corner_square_holes_card_00 {m : ℕ} (hm : 1 ≤ m)
    {w : Equiv.Perm (Fin (n_odd m))} (hw : IsValidOdd m w) :
    (holesFinset m w ∩ (Finset.Icc 1 (m : ℤ) ×ˢ Finset.Icc 1 (m : ℤ))).card =
      ∑ j ∈ Finset.range m, j := by
  have hpart : holesFinset m w ∩ (Finset.Icc 1 (m : ℤ) ×ˢ Finset.Icc 1 (m : ℤ)) =
      (Finset.Icc 1 (m : ℤ)).biUnion (fun y =>
        ((Finset.Icc 1 (m : ℤ)).filter (fun x => ¬ isCovered m w (x, y))).image
          (fun x => (x, y))) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_inter, mem_holesFinset, isHole, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx1, hxn, hy1, hyn, hnc⟩, ⟨_, hxm⟩, ⟨_, hym⟩⟩
      exact ⟨y, ⟨hy1, hym⟩, x, ⟨⟨hx1, hxm⟩, hnc⟩, rfl⟩
    · rintro ⟨y', ⟨hy1, hym⟩, x', ⟨⟨hx1, hxm⟩, hnc⟩, hxy⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
      have h2m := two_mul_m_le_n_odd hm
      exact ⟨⟨hx1, by omega, hy1, by omega, hnc⟩, ⟨hx1, hxm⟩, ⟨hy1, hym⟩⟩
  rw [hpart, Finset.card_biUnion]
  · have hsum : ∑ y ∈ Finset.Icc 1 (m : ℤ),
        (((Finset.Icc 1 (m : ℤ)).filter (fun x => ¬ isCovered m w (x, y))).image
          (fun x => (x, y))).card =
        ∑ j ∈ Finset.range m, j := by
      refine Finset.sum_bij (fun y _ => m - y.toNat) ?_ ?_ ?_ ?_
      · intro y hy; rw [Finset.mem_Icc] at hy; rw [Finset.mem_range]; omega
      · intro y₁ hy₁ y₂ hy₂ h; rw [Finset.mem_Icc] at hy₁ hy₂; omega
      · intro j hj
        rw [Finset.mem_range] at hj
        refine ⟨(m : ℤ) - (j : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro y hy
        rw [Finset.mem_Icc] at hy
        rw [Finset.card_image_of_injective _ (fun x₁ x₂ h => (Prod.mk.inj h).1)]
        simpa using corner_row_holes_00 hm hw hy.1 hy.2
    exact hsum
  · intro y₁ _ y₂ _ hne
    refine Finset.disjoint_left.mpr fun ⟨a, b⟩ ha hb => ?_
    simp only [Finset.mem_image] at ha hb
    obtain ⟨_, _, ha'⟩ := ha
    obtain ⟨_, _, hb'⟩ := hb
    have h1 : y₁ = b := (Prod.mk.inj ha').2
    have h2 : y₂ = b := (Prod.mk.inj hb').2
    exact hne (h1.trans h2.symm)

/-! ## Section 5: Step 4 — Zero Holes in the Central Box `C × C` (Claim 4) -/

private theorem sum_overhang_sub_one_tent (k : ℕ) :
    ∑ j ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), ((k : ℤ) - |j|) = (k : ℤ) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) =
        insert (-((k + 1 : ℕ) : ℤ)) (insert ((k + 1 : ℕ) : ℤ) (Finset.Icc (-(k : ℤ)) (k : ℤ))) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot1 : (-((k + 1 : ℕ) : ℤ)) ∉ insert ((k + 1 : ℕ) : ℤ) (Finset.Icc (-(k : ℤ)) (k : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot2 : ((k + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(k : ℤ)) (k : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    rw [h1, Finset.sum_insert hnot1, Finset.sum_insert hnot2]
    have ha1 : |-((k + 1 : ℕ) : ℤ)| = (k : ℤ) + 1 := by
      rw [abs_neg, abs_of_nonneg] <;> omega
    have ha2 : |((k + 1 : ℕ) : ℤ)| = (k : ℤ) + 1 := by
      rw [abs_of_nonneg] <;> omega
    rw [ha1, ha2]
    have hmid : ∑ j ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (((k + 1 : ℕ) : ℤ) - |j|) =
        ∑ j ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (((k : ℤ) - |j|) + 1) := by
      refine Finset.sum_congr rfl fun j _ => by push_cast; ring
    rw [hmid, Finset.sum_add_distrib, ih, Finset.sum_const, Int.card_Icc]
    have hcard : ((k : ℤ) + 1 - -(k : ℤ)).toNat = 2 * k + 1 := by omega
    rw [hcard, nsmul_eq_mul, mul_one]
    push_cast
    ring

private theorem sum_holesInCol_central {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) :
    ∑ x ∈ centralSet m, (holesInCol m w x).card = 2 * ∑ j ∈ Finset.range m, j ^ 2 := by
  have hunion := (claim1_supports_partition hm hw).1
  have hpd := (claim1_supports_partition hm hw).2
  have hz : (∑ x ∈ centralSet m, ((holesInCol m w x).card : ℤ)) =
      ∑ s : Fin m ⊕ Fin m, ∑ x ∈ oddSupport m hm w s, (overhang m hm w x - 1) := by
    have hcong : ∑ x ∈ centralSet m, ((holesInCol m w x).card : ℤ) =
        ∑ x ∈ centralSet m, (overhang m hm w x - 1) :=
      Finset.sum_congr rfl fun x hx => holesInCol_card_central hm hw hx
    rw [hcong, ← hunion, Finset.sum_biUnion (fun s₁ _ s₂ _ hne => hpd (Set.mem_univ s₁) (Set.mem_univ s₂) hne)]
  have heach : ∀ t : Fin m,
      (∑ x ∈ topSupport m hm w t, (overhang m hm w x - 1)) = ((m - 1 - t.val : ℕ) : ℤ) ^ 2 ∧
      (∑ x ∈ botSupport m hm w t, (overhang m hm w x - 1)) = ((m - 1 - t.val : ℕ) : ℤ) ^ 2 := by
    intro t
    have hht : tentHeight m t - 1 = ((m - 1 - t.val : ℕ) : ℤ) := by
      unfold tentHeight; have := t.isLt; omega
    have hsum_top : ∑ x ∈ topSupport m hm w t, (overhang m hm w x - 1) =
        ∑ x ∈ topSupport m hm w t, ((tentHeight m t - 1) - |x - topCol m hm w t|) :=
      Finset.sum_congr rfl fun x hx => by
        rw [overhang_eq_of_mem_topSupport hm hw hx]; ring
    have hsum_bot : ∑ x ∈ botSupport m hm w t, (overhang m hm w x - 1) =
        ∑ x ∈ botSupport m hm w t, ((tentHeight m t - 1) - |x - botCol m hm w t|) :=
      Finset.sum_congr rfl fun x hx => by
        rw [overhang_eq_of_mem_botSupport hm hw hx]; ring
    constructor
    · rw [hsum_top]
      have hbij : ∑ x ∈ topSupport m hm w t, ((tentHeight m t - 1) - |x - topCol m hm w t|) =
          ∑ j ∈ Finset.Icc (-((m - 1 - t.val : ℕ) : ℤ)) ((m - 1 - t.val : ℕ) : ℤ),
            (((m - 1 - t.val : ℕ) : ℤ) - |j|) := by
        refine Finset.sum_bij (fun x _ => x - topCol m hm w t) ?_ ?_ ?_ ?_
        · intro x hx; rw [mem_topSupport_iff, abs_le] at hx; rw [Finset.mem_Icc]; omega
        · intro x₁ _ x₂ _ h; omega
        · intro j hj
          rw [Finset.mem_Icc] at hj
          refine ⟨topCol m hm w t + j, mem_topSupport_iff.mpr ?_, by ring⟩
          rw [abs_le]; omega
        · intro x _; rw [hht]
      rw [hbij, sum_overhang_sub_one_tent]
    · rw [hsum_bot]
      have hbij : ∑ x ∈ botSupport m hm w t, ((tentHeight m t - 1) - |x - botCol m hm w t|) =
          ∑ j ∈ Finset.Icc (-((m - 1 - t.val : ℕ) : ℤ)) ((m - 1 - t.val : ℕ) : ℤ),
            (((m - 1 - t.val : ℕ) : ℤ) - |j|) := by
        refine Finset.sum_bij (fun x _ => x - botCol m hm w t) ?_ ?_ ?_ ?_
        · intro x hx; rw [mem_botSupport_iff, abs_le] at hx; rw [Finset.mem_Icc]; omega
        · intro x₁ _ x₂ _ h; omega
        · intro j hj
          rw [Finset.mem_Icc] at hj
          refine ⟨botCol m hm w t + j, mem_botSupport_iff.mpr ?_, by ring⟩
          rw [abs_le]; omega
        · intro x _; rw [hht]
      rw [hbij, sum_overhang_sub_one_tent]
  rw [Fintype.sum_sum_type] at hz
  have htop_sum : (∑ t : Fin m, ∑ x ∈ oddSupport m hm w (.inl t), (overhang m hm w x - 1)) =
      ∑ j ∈ Finset.range m, (j : ℤ) ^ 2 := by
    have h1 : (∑ t : Fin m, ∑ x ∈ topSupport m hm w t, (overhang m hm w x - 1)) =
        ∑ t : Fin m, ((m - 1 - t.val : ℕ) : ℤ) ^ 2 :=
      Finset.sum_congr rfl fun t _ => (heach t).1
    change (∑ t : Fin m, ∑ x ∈ topSupport m hm w t, (overhang m hm w x - 1)) = _
    rw [h1]
    refine Finset.sum_bij (fun t _ => m - 1 - t.val) ?_ ?_ ?_ ?_
    · intro t _; rw [Finset.mem_range]; have := t.isLt; omega
    · intro t₁ _ t₂ _ h; exact Fin.ext (by have := t₁.isLt; have := t₂.isLt; omega)
    · intro j hj; rw [Finset.mem_range] at hj; refine ⟨⟨m - 1 - j, by omega⟩, Finset.mem_univ _, by dsimp only; omega⟩
    · intro t _; rfl
  have hbot_sum : (∑ t : Fin m, ∑ x ∈ oddSupport m hm w (.inr t), (overhang m hm w x - 1)) =
      ∑ j ∈ Finset.range m, (j : ℤ) ^ 2 := by
    have h1 : (∑ t : Fin m, ∑ x ∈ botSupport m hm w t, (overhang m hm w x - 1)) =
        ∑ t : Fin m, ((m - 1 - t.val : ℕ) : ℤ) ^ 2 :=
      Finset.sum_congr rfl fun t _ => (heach t).2
    change (∑ t : Fin m, ∑ x ∈ botSupport m hm w t, (overhang m hm w x - 1)) = _
    rw [h1]
    refine Finset.sum_bij (fun t _ => m - 1 - t.val) ?_ ?_ ?_ ?_
    · intro t _; rw [Finset.mem_range]; have := t.isLt; omega
    · intro t₁ _ t₂ _ h; exact Fin.ext (by have := t₁.isLt; have := t₂.isLt; omega)
    · intro j hj; rw [Finset.mem_range] at hj; refine ⟨⟨m - 1 - j, by omega⟩, Finset.mem_univ _, by dsimp only; omega⟩
    · intro t _; rfl
  rw [htop_sum, hbot_sum, ← two_mul] at hz
  exact_mod_cast hz

/-- **Claim 4:** Every cell of the central box `C × C` is covered (`0` holes in `C × C`). -/
theorem claim4_central_box_covered {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {x y : ℤ} (hx : x ∈ centralSet m) (hy : y ∈ centralSet m) :
    isCovered m w (x, y) := by
  have h2m := two_mul_m_le_n_odd hm
  have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  let L : Finset ℤ := Finset.Icc 1 (m : ℤ)
  let R : Finset ℤ := Finset.Icc ((N_odd m : ℤ) - (m : ℤ)) (n_odd m : ℤ)
  let box : Finset ℤ := Finset.Icc 1 (n_odd m : ℤ)
  have hbox_part : box = L ∪ centralSet m ∪ R := by
    ext a
    simp only [box, L, R, centralSet, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj_LC : Disjoint L (centralSet m) := by
    refine Finset.disjoint_left.mpr fun a h1 h2 => ?_
    rw [Finset.mem_Icc] at h1; rw [mem_centralSet_iff] at h2; omega
  have hdisj_LR : Disjoint (L ∪ centralSet m) R := by
    refine Finset.disjoint_left.mpr fun a h1 h2 => ?_
    simp only [L, Finset.mem_union, Finset.mem_Icc, mem_centralSet_iff] at h1
    rw [Finset.mem_Icc] at h2
    omega
  have hholes_col_eq : ∀ u : ℤ, (holesFinset m w ∩ ({u} ×ˢ box)).card =
      if u ∈ box then (holesInCol m w u).card else 0 := by
    intro u
    split_ifs with hu
    · refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
      · rintro ⟨px, py⟩ hp
        simp only [Finset.mem_inter, mem_holesFinset, Finset.mem_product,
          Finset.mem_singleton] at hp
        rcases hp with ⟨hhole, rfl, hpy⟩
        exact mem_holesInCol.mpr ⟨hhole.2.2.1, hhole.2.2.2.1, hhole.2.2.2.2⟩
      · rintro ⟨x₁, y₁⟩ h1 ⟨x₂, y₂⟩ h2 h
        simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton] at h1 h2
        exact Prod.ext (h1.2.1.trans h2.2.1.symm) h
      · intro py hpy
        rw [mem_holesInCol] at hpy
        rw [Finset.mem_Icc] at hu
        refine ⟨(u, py), ?_, rfl⟩
        simp only [Finset.mem_inter, mem_holesFinset, isHole, Finset.mem_product,
          Finset.mem_singleton, box, Finset.mem_Icc]
        exact ⟨⟨hu.1, hu.2, hpy.1, hpy.2.1, hpy.2.2⟩, trivial, ⟨hpy.1, hpy.2.1⟩⟩
    · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      rintro ⟨px, py⟩ hp
      simp only [Finset.mem_inter, mem_holesFinset, isHole, Finset.mem_product,
        Finset.mem_singleton] at hp
      rcases hp with ⟨hhole, rfl, _⟩
      exact hu (Finset.mem_Icc.mpr ⟨hhole.1, hhole.2.1⟩)
  -- Express (holesFinset m w).card by columns
  have hcol_split : ∀ S : Finset ℤ, S ⊆ box →
      (holesFinset m w ∩ (S ×ˢ box)).card = ∑ u ∈ S, (holesInCol m w u).card := by
    intro S hS
    have hbi : holesFinset m w ∩ (S ×ˢ box) =
        S.biUnion (fun u => holesFinset m w ∩ ({u} ×ˢ box)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2a, h2b⟩; exact ⟨a, h2a, h1, rfl, h2b⟩
      · rintro ⟨u, hu, h1, rfl, h2b⟩; exact ⟨h1, hu, h2b⟩
    rw [hbi, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun u hu => ?_
      rw [hholes_col_eq u]
      split_ifs with hmem
      · rfl
      · exact absurd (hS hu) hmem
    · intro u₁ _ u₂ _ hne
      refine Finset.disjoint_left.mpr fun ⟨a, b⟩ ha hb => ?_
      simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton] at ha hb
      exact hne (ha.2.1.symm.trans hb.2.1)
  have hrow_split : ∀ S : Finset ℤ, S ⊆ box →
      (holesFinset m w ∩ (box ×ˢ S)).card = ∑ v ∈ S, (holesInRow m w v).card := by
    intro S hS
    have hbi : holesFinset m w ∩ (box ×ˢ S) =
        S.biUnion (fun v => holesFinset m w ∩ (box ×ˢ {v})) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2a, h2b⟩; exact ⟨b, h2b, h1, h2a, rfl⟩
      · rintro ⟨v, hv, h1, h2a, rfl⟩; exact ⟨h1, h2a, hv⟩
    rw [hbi, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun v hv => ?_
      refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
      · rintro ⟨px, py⟩ hp
        simp only [Finset.mem_inter, mem_holesFinset, isHole, Finset.mem_product,
          Finset.mem_singleton] at hp
        rcases hp with ⟨hhole, _, rfl⟩
        exact mem_holesInRow.mpr ⟨hhole.1, hhole.2.1, hhole.2.2.2.2⟩
      · rintro ⟨x₁, y₁⟩ h1 ⟨x₂, y₂⟩ h2 h
        simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton] at h1 h2
        exact Prod.ext h (h1.2.2.trans h2.2.2.symm)
      · intro px hpx
        rw [mem_holesInRow] at hpx
        have hv' := Finset.mem_Icc.mp (hS hv)
        refine ⟨(px, v), ?_, rfl⟩
        simp only [Finset.mem_inter, mem_holesFinset, isHole, Finset.mem_product,
          Finset.mem_singleton, box, Finset.mem_Icc]
        exact ⟨⟨hpx.1, hpx.2.1, hv'.1, hv'.2, hpx.2.2⟩, ⟨hpx.1, hpx.2.1⟩, trivial⟩
    · intro v₁ _ v₂ _ hne
      refine Finset.disjoint_left.mpr fun ⟨a, b⟩ ha hb => ?_
      simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton] at ha hb
      exact hne (ha.2.2.symm.trans hb.2.2)
  -- Side column sums
  have hL_sum : ∑ u ∈ L, (holesInCol m w u).card = ∑ j ∈ Finset.range m, ((j + 1) ^ 2 - 1) := by
    refine Finset.sum_bij (fun u _ => (m : ℤ) - u |>.toNat) ?_ ?_ ?_ ?_
    · intro u hu; rw [Finset.mem_Icc] at hu; rw [Finset.mem_range]; omega
    · intro u₁ hu₁ u₂ hu₂ h; rw [Finset.mem_Icc] at hu₁ hu₂; omega
    · intro j hj; rw [Finset.mem_range] at hj
      refine ⟨(m : ℤ) - (j : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro u hu
      rw [Finset.mem_Icc] at hu
      have hu_eq : u = (m : ℤ) + 1 - (((m - u.toNat) + 1 : ℕ) : ℤ) := by omega
      have hcard := claim2_left_side_col_holes hm hw (s := (m - u.toNat) + 1) (by omega) (by omega)
      have harg : (m : ℤ) + 1 - (((m - u.toNat) + 1 : ℕ) : ℤ) = u := by omega
      rw [harg] at hcard
      have hs_eq : (m - u.toNat) + 1 = ((m : ℤ) - u).toNat + 1 := by omega
      rw [hcard, hs_eq]
  have hR_sum : ∑ u ∈ R, (holesInCol m w u).card = ∑ j ∈ Finset.range m, ((j + 1) ^ 2 - 1) := by
    have hbij : ∑ u ∈ R, (holesInCol m w u).card =
        ∑ u ∈ L, (holesInCol m (permReverse w) u).card := by
      refine Finset.sum_bij (fun u _ => (N_odd m : ℤ) - u) ?_ ?_ ?_ ?_
      · intro u hu; rw [Finset.mem_Icc] at hu ⊢; omega
      · intro _ _ _ _ h; omega
      · intro u hu; rw [Finset.mem_Icc] at hu
        refine ⟨(N_odd m : ℤ) - u, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by ring⟩
      · intro u _
        rw [holesInCol_card_permReverse]
        congr 1; ring_nf
    rw [hbij]
    -- Apply hL_sum pattern to permReverse w
    have hL_rev : ∑ u ∈ L, (holesInCol m (permReverse w) u).card =
        ∑ j ∈ Finset.range m, ((j + 1) ^ 2 - 1) := by
      refine Finset.sum_bij (fun u _ => (m : ℤ) - u |>.toNat) ?_ ?_ ?_ ?_
      · intro u hu; rw [Finset.mem_Icc] at hu; rw [Finset.mem_range]; omega
      · intro u₁ hu₁ u₂ hu₂ h; rw [Finset.mem_Icc] at hu₁ hu₂; omega
      · intro j hj; rw [Finset.mem_range] at hj
        refine ⟨(m : ℤ) - (j : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro u hu
        rw [Finset.mem_Icc] at hu
        have hcard := claim2_left_side_col_holes hm (isValidPerm_permReverse hw)
          (s := (m - u.toNat) + 1) (by omega) (by omega)
        have harg : (m : ℤ) + 1 - (((m - u.toNat) + 1 : ℕ) : ℤ) = u := by omega
        rw [harg] at hcard
        have hs_eq : (m - u.toNat) + 1 = ((m : ℤ) - u).toNat + 1 := by omega
        rw [hcard, hs_eq]
    exact hL_rev
  -- Side row sums = side col sums of permInverse w
  have hLR_row_sum : ∑ v ∈ L ∪ R, (holesInRow m w v).card =
      2 * ∑ j ∈ Finset.range m, ((j + 1) ^ 2 - 1) := by
    have hdisj : Disjoint L R := by
      refine Finset.disjoint_left.mpr fun a h1 h2 => ?_
      rw [Finset.mem_Icc] at h1 h2; omega
    rw [Finset.sum_union hdisj]
    have hL_row : ∑ v ∈ L, (holesInRow m w v).card = ∑ j ∈ Finset.range m, ((j + 1) ^ 2 - 1) := by
      refine Finset.sum_bij (fun v _ => (m : ℤ) - v |>.toNat) ?_ ?_ ?_ ?_
      · intro v hv; rw [Finset.mem_Icc] at hv; rw [Finset.mem_range]; omega
      · intro v₁ hv₁ v₂ hv₂ h; rw [Finset.mem_Icc] at hv₁ hv₂; omega
      · intro j hj; rw [Finset.mem_range] at hj
        refine ⟨(m : ℤ) - (j : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro v hv
        rw [Finset.mem_Icc] at hv
        have hcard := claim2_bot_side_row_holes hm hw (s := (m - v.toNat) + 1) (by omega) (by omega)
        have harg : (m : ℤ) + 1 - (((m - v.toNat) + 1 : ℕ) : ℤ) = v := by omega
        rw [harg] at hcard
        have hs_eq : (m - v.toNat) + 1 = ((m : ℤ) - v).toNat + 1 := by omega
        rw [hcard, hs_eq]
    have hR_row : ∑ v ∈ R, (holesInRow m w v).card = ∑ j ∈ Finset.range m, ((j + 1) ^ 2 - 1) := by
      refine Finset.sum_bij (fun v _ => (m : ℤ) - ((N_odd m : ℤ) - v) |>.toNat) ?_ ?_ ?_ ?_
      · intro v hv; rw [Finset.mem_Icc] at hv; rw [Finset.mem_range]; omega
      · intro v₁ hv₁ v₂ hv₂ h; rw [Finset.mem_Icc] at hv₁ hv₂; omega
      · intro j hj; rw [Finset.mem_range] at hj
        refine ⟨(N_odd m : ℤ) - ((m : ℤ) - (j : ℤ)), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro v hv
        rw [Finset.mem_Icc] at hv
        have hcard := claim2_top_side_row_holes hm hw
          (s := (m - ((N_odd m : ℤ) - v).toNat) + 1) (by omega) (by omega)
        have harg : (N_odd m : ℤ) - ((m : ℤ) + 1 -
            (((m - ((N_odd m : ℤ) - v).toNat) + 1 : ℕ) : ℤ)) = v := by omega
        rw [harg] at hcard
        have hs_eq : (m - ((N_odd m : ℤ) - v).toNat) + 1 =
            ((m : ℤ) - ((N_odd m : ℤ) - v)).toNat + 1 := by omega
        rw [hcard, hs_eq]
    rw [hL_row, hR_row, two_mul]
  -- 4 corner squares via symmetries
  have hc_10 : (holesFinset m w ∩ (R ×ˢ L)).card = ∑ j ∈ Finset.range m, j := by
    have hbij : (holesFinset m w ∩ (R ×ˢ L)).card =
        (holesFinset m (permReverse w) ∩ (L ×ˢ L)).card := by
      refine Finset.card_bij (fun p _ => ptFlipX (N_odd m : ℤ) p) ?_ ?_ ?_
      · rintro ⟨a, b⟩ hp
        simp only [Finset.mem_inter, mem_holesFinset, Finset.mem_product, L, R, Finset.mem_Icc,
          ptFlipX] at hp ⊢
        refine ⟨(isHole_permReverse w (N_odd m - a, b)).mpr ?_, ⟨by omega, by omega⟩, hp.2.2⟩
        unfold ptFlipX; simpa using hp.1
      · rintro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
        simp only [ptFlipX] at h
        exact Prod.ext (by have := (Prod.mk.inj h).1; omega) (Prod.mk.inj h).2
      · rintro ⟨a, b⟩ hp
        simp only [Finset.mem_inter, mem_holesFinset, Finset.mem_product, L, Finset.mem_Icc] at hp
        refine ⟨((N_odd m : ℤ) - a, b), ?_, ?_⟩
        · simp only [Finset.mem_inter, mem_holesFinset, Finset.mem_product, L, R, Finset.mem_Icc]
          refine ⟨(isHole_permReverse w (a, b)).mp hp.1, ⟨by omega, by omega⟩, hp.2.2⟩
        · unfold ptFlipX; exact Prod.ext (by dsimp only; ring) rfl
    rw [hbij]
    exact corner_square_holes_card_00 hm (isValidPerm_permReverse hw)
  have hc_01 : (holesFinset m w ∩ (L ×ˢ R)).card = ∑ j ∈ Finset.range m, j := by
    have hbij : (holesFinset m w ∩ (L ×ˢ R)).card =
        (holesFinset m (permComplement w) ∩ (L ×ˢ L)).card := by
      refine Finset.card_bij (fun p _ => ptFlipY (N_odd m : ℤ) p) ?_ ?_ ?_
      · rintro ⟨a, b⟩ hp
        simp only [Finset.mem_inter, mem_holesFinset, Finset.mem_product, L, R, Finset.mem_Icc,
          ptFlipY] at hp ⊢
        refine ⟨(isHole_permComplement w (a, N_odd m - b)).mpr ?_, hp.2.1, ⟨by omega, by omega⟩⟩
        unfold ptFlipY; simpa using hp.1
      · rintro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
        simp only [ptFlipY] at h
        exact Prod.ext (Prod.mk.inj h).1 (by have := (Prod.mk.inj h).2; omega)
      · rintro ⟨a, b⟩ hp
        simp only [Finset.mem_inter, mem_holesFinset, Finset.mem_product, L, Finset.mem_Icc] at hp
        refine ⟨(a, (N_odd m : ℤ) - b), ?_, ?_⟩
        · simp only [Finset.mem_inter, mem_holesFinset, Finset.mem_product, L, R, Finset.mem_Icc]
          refine ⟨(isHole_permComplement w (a, b)).mp hp.1, hp.2.1, ⟨by omega, by omega⟩⟩
        · unfold ptFlipY; exact Prod.ext rfl (by dsimp only; ring)
    rw [hbij]
    exact corner_square_holes_card_00 hm (isValidPerm_permComplement hw)
  have hc_11 : (holesFinset m w ∩ (R ×ˢ R)).card = ∑ j ∈ Finset.range m, j := by
    have hbij : (holesFinset m w ∩ (R ×ˢ R)).card =
        (holesFinset m (permReverse (permComplement w)) ∩ (L ×ˢ L)).card := by
      refine Finset.card_bij (fun p _ => ptFlipX (N_odd m : ℤ) (ptFlipY (N_odd m : ℤ) p)) ?_ ?_ ?_
      · rintro ⟨a, b⟩ hp
        simp only [Finset.mem_inter, mem_holesFinset, Finset.mem_product, L, R, Finset.mem_Icc,
          ptFlipX, ptFlipY] at hp ⊢
        refine ⟨(isHole_permReverse (permComplement w) _).mpr
          ((isHole_permComplement w _).mpr ?_), ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
        unfold ptFlipX ptFlipY; simpa using hp.1
      · rintro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
        simp only [ptFlipX, ptFlipY] at h
        exact Prod.ext (by have := (Prod.mk.inj h).1; omega) (by have := (Prod.mk.inj h).2; omega)
      · rintro ⟨a, b⟩ hp
        simp only [Finset.mem_inter, mem_holesFinset, Finset.mem_product, L, Finset.mem_Icc] at hp
        refine ⟨((N_odd m : ℤ) - a, (N_odd m : ℤ) - b), ?_, ?_⟩
        · simp only [Finset.mem_inter, mem_holesFinset, Finset.mem_product, R, Finset.mem_Icc]
          have h1 : isHole m (permComplement w) ((N_odd m : ℤ) - a, b) := by
            simpa [ptFlipX] using (isHole_permReverse (permComplement w) (a, b)).mp hp.1
          have h2 : isHole m w ((N_odd m : ℤ) - a, (N_odd m : ℤ) - b) := by
            simpa [ptFlipY] using (isHole_permComplement w ((N_odd m : ℤ) - a, b)).mp h1
          exact ⟨h2, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
        · unfold ptFlipX ptFlipY; ext <;> dsimp only <;> ring
    rw [hbij]
    exact corner_square_holes_card_00 hm (isValidPerm_permReverse (isValidPerm_permComplement hw))
  -- Total holes H = (holesFinset m w).card
  have hH_box : holesFinset m w = holesFinset m w ∩ (box ×ˢ box) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_inter, mem_holesFinset, isHole, Finset.mem_product, box, Finset.mem_Icc]
    tauto
  have hH : (holesFinset m w).card =
      2 * ∑ j ∈ Finset.range m, j ^ 2 + 2 * ∑ j ∈ Finset.range m, ((j + 1) ^ 2 - 1) := by
    rw [hH_box, hcol_split box (Finset.Subset.refl _), hbox_part,
      Finset.sum_union hdisj_LR, Finset.sum_union hdisj_LC,
      hL_sum, hR_sum, sum_holesInCol_central hm hw]
    omega
  -- Now partition holesFinset m w into (C × C), (sideCols × box), (C × sideRows)
  let side := L ∪ R
  have hside_sub : side ⊆ box := by
    intro a ha; simp only [side, L, R, box, Finset.mem_union, Finset.mem_Icc] at ha ⊢; omega
  have hC_sub : centralSet m ⊆ box := by
    intro a ha; simp only [centralSet, box, Finset.mem_Icc] at ha ⊢; omega
  have hdisj_sideC : Disjoint side (centralSet m) := by
    refine Finset.disjoint_left.mpr fun a h1 h2 => ?_
    simp only [side, L, R, Finset.mem_union, Finset.mem_Icc, mem_centralSet_iff] at h1 h2
    omega
  have hbox_sc : box = side ∪ centralSet m := by
    ext a; simp only [side, box, L, R, centralSet, Finset.mem_union, Finset.mem_Icc]; omega
  have hholes_decomp : (holesFinset m w).card =
      (holesFinset m w ∩ (centralSet m ×ˢ centralSet m)).card +
      (holesFinset m w ∩ (side ×ˢ box)).card +
      (holesFinset m w ∩ (centralSet m ×ˢ side)).card := by
    have heq : holesFinset m w =
        (holesFinset m w ∩ (centralSet m ×ˢ centralSet m)) ∪
        ((holesFinset m w ∩ (side ×ˢ box)) ∪ (holesFinset m w ∩ (centralSet m ×ˢ side))) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_product]
      constructor
      · intro hhole
        have hbox_mem : (a, b) ∈ box ×ˢ box := by
          rw [hH_box, Finset.mem_inter] at hhole; exact hhole.2
        rcases Finset.mem_product.mp hbox_mem with ⟨ha_b, hb_b⟩
        rcases Finset.mem_union.mp (hbox_sc ▸ ha_b) with has | hac
        · exact Or.inr (Or.inl ⟨hhole, has, hb_b⟩)
        · rcases Finset.mem_union.mp (hbox_sc ▸ hb_b) with hbs | hbc
          · exact Or.inr (Or.inr ⟨hhole, hac, hbs⟩)
          · exact Or.inl ⟨hhole, hac, hbc⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hd1 : Disjoint (holesFinset m w ∩ (centralSet m ×ˢ centralSet m))
        ((holesFinset m w ∩ (side ×ˢ box)) ∪ (holesFinset m w ∩ (centralSet m ×ˢ side))) := by
      refine Finset.disjoint_left.mpr fun ⟨a, b⟩ h1 h2 => ?_
      simp only [Finset.mem_inter, Finset.mem_product] at h1
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_product] at h2
      rcases h2 with h2 | h2
      · exact Finset.disjoint_left.mp hdisj_sideC h2.2.1 h1.2.1
      · exact Finset.disjoint_left.mp hdisj_sideC h2.2.2 h1.2.2
    have hd2 : Disjoint (holesFinset m w ∩ (side ×ˢ box)) (holesFinset m w ∩ (centralSet m ×ˢ side)) := by
      refine Finset.disjoint_left.mpr fun ⟨a, b⟩ h1 h2 => ?_
      simp only [Finset.mem_inter, Finset.mem_product] at h1 h2
      exact Finset.disjoint_left.mp hdisj_sideC h1.2.1 h2.2.1
    calc
      (holesFinset m w).card
        = ((holesFinset m w ∩ (centralSet m ×ˢ centralSet m)) ∪
            ((holesFinset m w ∩ (side ×ˢ box)) ∪
              (holesFinset m w ∩ (centralSet m ×ˢ side)))).card := congrArg Finset.card heq
      _ = (holesFinset m w ∩ (centralSet m ×ˢ centralSet m)).card +
            ((holesFinset m w ∩ (side ×ˢ box)) ∪
              (holesFinset m w ∩ (centralSet m ×ˢ side))).card := Finset.card_union_of_disjoint hd1
      _ = (holesFinset m w ∩ (centralSet m ×ˢ centralSet m)).card +
            ((holesFinset m w ∩ (side ×ˢ box)).card +
              (holesFinset m w ∩ (centralSet m ×ˢ side)).card) := by
          rw [Finset.card_union_of_disjoint hd2]
      _ = (holesFinset m w ∩ (centralSet m ×ˢ centralSet m)).card +
            (holesFinset m w ∩ (side ×ˢ box)).card +
            (holesFinset m w ∩ (centralSet m ×ˢ side)).card := by ring
  -- Also (holes ∩ (box × side)) = (holes ∩ (side × side)) ∪ (holes ∩ (C × side))
  have hrow_decomp : (holesFinset m w ∩ (box ×ˢ side)).card =
      (holesFinset m w ∩ (side ×ˢ side)).card +
      (holesFinset m w ∩ (centralSet m ×ˢ side)).card := by
    have heq : holesFinset m w ∩ (box ×ˢ side) =
        (holesFinset m w ∩ (side ×ˢ side)) ∪ (holesFinset m w ∩ (centralSet m ×ˢ side)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_product]
      constructor
      · rintro ⟨hh, ha_b, hb_s⟩
        rcases Finset.mem_union.mp (hbox_sc ▸ ha_b) with has | hac
        · exact Or.inl ⟨hh, has, hb_s⟩
        · exact Or.inr ⟨hh, hac, hb_s⟩
      · rintro (⟨hh, has, hb_s⟩ | ⟨hh, hac, hb_s⟩)
        · exact ⟨hh, hside_sub has, hb_s⟩
        · exact ⟨hh, hC_sub hac, hb_s⟩
    have hd : Disjoint (holesFinset m w ∩ (side ×ˢ side)) (holesFinset m w ∩ (centralSet m ×ˢ side)) := by
      refine Finset.disjoint_left.mpr fun ⟨a, b⟩ h1 h2 => ?_
      simp only [Finset.mem_inter, Finset.mem_product] at h1 h2
      exact Finset.disjoint_left.mp hdisj_sideC h1.2.1 h2.2.1
    rw [heq, Finset.card_union_of_disjoint hd]
  have hside_sq : (holesFinset m w ∩ (side ×ˢ side)).card = 4 * ∑ j ∈ Finset.range m, j := by
    have hdisj_LR_side : Disjoint L R := by
      refine Finset.disjoint_left.mpr fun a h1 h2 => ?_
      rw [Finset.mem_Icc] at h1 h2; omega
    have hpart4 : holesFinset m w ∩ (side ×ˢ side) =
        ((holesFinset m w ∩ (L ×ˢ L)) ∪ (holesFinset m w ∩ (R ×ˢ L))) ∪
        ((holesFinset m w ∩ (L ×ˢ R)) ∪ (holesFinset m w ∩ (R ×ˢ R))) := by
      ext ⟨a, b⟩
      simp only [side, Finset.mem_union, Finset.mem_inter, Finset.mem_product]
      constructor
      · rintro ⟨hh, ha | ha, hb | hb⟩
        · exact Or.inl (Or.inl ⟨hh, ha, hb⟩)
        · exact Or.inr (Or.inl ⟨hh, ha, hb⟩)
        · exact Or.inl (Or.inr ⟨hh, ha, hb⟩)
        · exact Or.inr (Or.inr ⟨hh, ha, hb⟩)
      · rintro ((⟨hh, ha, hb⟩ | ⟨hh, ha, hb⟩) | (⟨hh, ha, hb⟩ | ⟨hh, ha, hb⟩))
        · exact ⟨hh, Or.inl ha, Or.inl hb⟩
        · exact ⟨hh, Or.inr ha, Or.inl hb⟩
        · exact ⟨hh, Or.inl ha, Or.inr hb⟩
        · exact ⟨hh, Or.inr ha, Or.inr hb⟩
    rw [hpart4, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint]
    · rw [corner_square_holes_card_00 hm hw, hc_10, hc_01, hc_11]; ring
    · refine Finset.disjoint_left.mpr fun ⟨a, b⟩ ha hb => ?_
      simp only [Finset.mem_inter, Finset.mem_product] at ha hb
      exact Finset.disjoint_left.mp hdisj_LR_side ha.2.1 hb.2.1
    · refine Finset.disjoint_left.mpr fun ⟨a, b⟩ ha hb => ?_
      simp only [Finset.mem_inter, Finset.mem_product] at ha hb
      exact Finset.disjoint_left.mp hdisj_LR_side ha.2.1 hb.2.1
    · refine Finset.disjoint_left.mpr fun ⟨a, b⟩ ha hb => ?_
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_product] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact Finset.disjoint_left.mp hdisj_LR_side ha.2.2 hb.2.2
      · exact Finset.disjoint_left.mp hdisj_LR_side ha.2.2 hb.2.2
      · exact Finset.disjoint_left.mp hdisj_LR_side ha.2.2 hb.2.2
      · exact Finset.disjoint_left.mp hdisj_LR_side ha.2.2 hb.2.2
  have hside_col : (holesFinset m w ∩ (side ×ˢ box)).card =
      2 * ∑ j ∈ Finset.range m, ((j + 1) ^ 2 - 1) := by
    rw [hcol_split side hside_sub, Finset.sum_union (by
      refine Finset.disjoint_left.mpr fun a h1 h2 => ?_
      rw [Finset.mem_Icc] at h1 h2; omega)]
    rw [hL_sum, hR_sum, two_mul]
  have hside_row : (holesFinset m w ∩ (box ×ˢ side)).card =
      2 * ∑ j ∈ Finset.range m, ((j + 1) ^ 2 - 1) := by
    rw [hrow_split side hside_sub, hLR_row_sum]
  have hsum_id :
      2 * ∑ j ∈ Finset.range m, j ^ 2 + 2 * ∑ j ∈ Finset.range m, ((j + 1) ^ 2 - 1) +
        4 * ∑ j ∈ Finset.range m, j =
      4 * ∑ j ∈ Finset.range m, ((j + 1) ^ 2 - 1) := by
    have hterm : ∀ j ∈ Finset.range m,
        2 * j ^ 2 + 2 * ((j + 1) ^ 2 - 1) + 4 * j = 4 * ((j + 1) ^ 2 - 1) := by
      intro j _
      have hj1 : 1 ≤ (j + 1) ^ 2 := Nat.one_le_pow 2 (j + 1) (by omega)
      zify [hj1]
      ring
    calc
      2 * ∑ j ∈ Finset.range m, j ^ 2 + 2 * ∑ j ∈ Finset.range m, ((j + 1) ^ 2 - 1) +
          4 * ∑ j ∈ Finset.range m, j
        = ∑ j ∈ Finset.range m, (2 * j ^ 2 + 2 * ((j + 1) ^ 2 - 1) + 4 * j) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = ∑ j ∈ Finset.range m, 4 * ((j + 1) ^ 2 - 1) := Finset.sum_congr rfl hterm
      _ = 4 * ∑ j ∈ Finset.range m, ((j + 1) ^ 2 - 1) := by rw [← Finset.mul_sum]
  have hC_card0 : (holesFinset m w ∩ (centralSet m ×ˢ centralSet m)).card = 0 := by
    omega
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hC_card0
  by_contra hnc
  apply hC_card0 (x, y)
  simp only [Finset.mem_inter, mem_holesFinset, isHole, Finset.mem_product]
  rw [mem_centralSet_iff] at hx hy
  exact ⟨⟨by omega, by omega, by omega, by omega, hnc⟩,
    mem_centralSet_iff.mpr hx, mem_centralSet_iff.mpr hy⟩

/-! ## Section 6: Step 5 — Central Column Holes Sit at One End (Claim 5) -/

private theorem central_top_overhang_count {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {y : ℕ} (hy1 : 1 ≤ y) (hym : y ≤ m) :
    ((centralSet m).filter (fun x => isTopCol m hm w x ∧ (y : ℤ) + 1 ≤ overhang m hm w x)).card =
      (m - y) ^ 2 := by
  have hunion := (claim1_supports_partition hm hw).1
  have hpd := (claim1_supports_partition hm hw).2
  have hpart : (centralSet m).filter (fun x => isTopCol m hm w x ∧ (y : ℤ) + 1 ≤ overhang m hm w x) =
      (Finset.univ : Finset (Fin m)).biUnion (fun t =>
        (topSupport m hm w t).filter (fun x => (y : ℤ) + 1 ≤ tentHeight m t - |x - topCol m hm w t|)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨t, ht⟩, hge⟩
      refine ⟨t, ht, ?_⟩
      rwa [← overhang_eq_of_mem_topSupport hm hw ht]
    · rintro ⟨t, ht, hge⟩
      refine ⟨topSupport_subset_central hm hw t ht, ⟨t, ht⟩, ?_⟩
      rwa [overhang_eq_of_mem_topSupport hm hw ht]
  rw [hpart, Finset.card_biUnion]
  · have hterm : ∀ t : Fin m,
        ((topSupport m hm w t).filter
          (fun x => (y : ℤ) + 1 ≤ tentHeight m t - |x - topCol m hm w t|)).card =
        if y < m - t.val then 2 * ((m - t.val) - y) - 1 else 0 := by
      intro t
      split_ifs with hlt
      · have heq : (topSupport m hm w t).filter
            (fun x => (y : ℤ) + 1 ≤ tentHeight m t - |x - topCol m hm w t|) =
            Finset.Icc (topCol m hm w t - (tentHeight m t - (y : ℤ) - 1))
              (topCol m hm w t + (tentHeight m t - (y : ℤ) - 1)) := by
          ext x
          have hle : (y : ℤ) + 1 ≤ tentHeight m t - |x - topCol m hm w t| ↔
              |x - topCol m hm w t| ≤ tentHeight m t - (y : ℤ) - 1 := by omega
          simp only [Finset.mem_filter, mem_topSupport_iff, hle, Finset.mem_Icc, abs_le]
          unfold tentHeight
          omega
        rw [heq, Int.card_Icc]
        unfold tentHeight
        omega
      · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro x hx
        simp only [Finset.mem_filter] at hx
        have hnonneg : 0 ≤ |x - topCol m hm w t| := abs_nonneg _
        unfold tentHeight at hx
        omega
    have hsum : (∑ t : Fin m, ((topSupport m hm w t).filter
          (fun x => (y : ℤ) + 1 ≤ tentHeight m t - |x - topCol m hm w t|)).card) =
        ∑ k ∈ Finset.range (m - y), (2 * k + 1) := by
      have hcongr : ∑ t : Fin m, ((topSupport m hm w t).filter
            (fun x => (y : ℤ) + 1 ≤ tentHeight m t - |x - topCol m hm w t|)).card =
          ∑ t ∈ (Finset.univ : Finset (Fin m)).filter (fun t : Fin m => y < m - t.val),
            (2 * ((m - t.val) - y) - 1) := by
        rw [← Finset.sum_subset (Finset.filter_subset
            (fun t : Fin m => y < m - t.val) Finset.univ)]
        · refine Finset.sum_congr rfl fun t ht => ?_
          rw [Finset.mem_filter] at ht
          rw [hterm t]; simp [ht.2]
        · intro t _ hnot
          rw [Finset.mem_filter, not_and] at hnot
          have hle : ¬ y < m - t.val := fun h => hnot (Finset.mem_univ _) h
          rw [hterm t]; simp [hle]
      rw [hcongr]
      refine Finset.sum_bij (fun t _ => m - t.val - y - 1) ?_ ?_ ?_ ?_
      · intro t ht; rw [Finset.mem_filter] at ht; rw [Finset.mem_range]; omega
      · intro t₁ ht₁ t₂ ht₂ h
        rw [Finset.mem_filter] at ht₁ ht₂
        exact Fin.ext (by omega)
      · intro k hk
        rw [Finset.mem_range] at hk
        refine ⟨⟨m - (y + k + 1), by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
      · intro t ht; rw [Finset.mem_filter] at ht; omega
    rw [hsum, sum_range_two_mul_add_one]
  · intro t₁ _ t₂ _ hne
    have hdisj := hpd (Set.mem_univ (.inl t₁)) (Set.mem_univ (.inl t₂)) (by simp [hne])
    exact hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

private theorem row_central_holes_card {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {y : ℕ} (hy1 : 1 ≤ y) (hym : y ≤ m) :
    ((centralSet m).filter (fun x => ¬ isCovered m w (x, (y : ℤ)))).card = (m - y) ^ 2 := by
  have h2m := two_mul_m_le_n_odd hm
  have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  let L : Finset ℤ := Finset.Icc 1 (m : ℤ)
  let R : Finset ℤ := Finset.Icc ((N_odd m : ℤ) - (m : ℤ)) (n_odd m : ℤ)
  let box : Finset ℤ := Finset.Icc 1 (n_odd m : ℤ)
  have hbox_part : box = L ∪ centralSet m ∪ R := by
    ext x; simp only [box, L, R, centralSet, Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj_LC : Disjoint L (centralSet m) := by
    refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    rw [Finset.mem_Icc] at h1; rw [mem_centralSet_iff] at h2; omega
  have hdisj_LR : Disjoint (L ∪ centralSet m) R := by
    refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    simp only [L, Finset.mem_union, Finset.mem_Icc, mem_centralSet_iff] at h1
    rw [Finset.mem_Icc] at h2
    omega
  have htot : (holesInRow m w (y : ℤ)).card = (m + 1 - y) ^ 2 - 1 := by
    have hcard := claim2_bot_side_row_holes hm hw (s := m + 1 - y) (by omega) (by omega)
    have heq : (m : ℤ) + 1 - ((m + 1 - y : ℕ) : ℤ) = (y : ℤ) := by omega
    rwa [heq] at hcard
  have hsplit : holesInRow m w (y : ℤ) =
      (L.filter (fun x => ¬ isCovered m w (x, (y : ℤ)))) ∪
      ((centralSet m).filter (fun x => ¬ isCovered m w (x, (y : ℤ)))) ∪
      (R.filter (fun x => ¬ isCovered m w (x, (y : ℤ)))) := by
    ext x
    simp only [mem_holesInRow, Finset.mem_union, Finset.mem_filter, L, R, centralSet, Finset.mem_Icc]
    have hpart : (1 ≤ x ∧ x ≤ (n_odd m : ℤ)) ↔
        (1 ≤ x ∧ x ≤ (m : ℤ)) ∨ ((m : ℤ) + 1 ≤ x ∧ x ≤ (n_odd m : ℤ) - (m : ℤ)) ∨
          ((N_odd m : ℤ) - (m : ℤ) ≤ x ∧ x ≤ (n_odd m : ℤ)) := by omega
    tauto
  have hd1' : Disjoint (L.filter (fun x => ¬ isCovered m w (x, (y : ℤ))))
      ((centralSet m).filter (fun x => ¬ isCovered m w (x, (y : ℤ)))) :=
    hdisj_LC.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hd2' : Disjoint (L.filter (fun x => ¬ isCovered m w (x, (y : ℤ))) ∪
        (centralSet m).filter (fun x => ¬ isCovered m w (x, (y : ℤ))))
      (R.filter (fun x => ¬ isCovered m w (x, (y : ℤ)))) :=
    hdisj_LR.mono
      (Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      (Finset.filter_subset _ _)
  have hL : (L.filter (fun x => ¬ isCovered m w (x, (y : ℤ)))).card = m - y := by
    simpa [L] using corner_row_holes_00 hm hw (y := (y : ℤ)) (by omega) (by omega)
  have hR : (R.filter (fun x => ¬ isCovered m w (x, (y : ℤ)))).card = m - y := by
    have hbij : (R.filter (fun x => ¬ isCovered m w (x, (y : ℤ)))).card =
        (L.filter (fun x => ¬ isCovered m (permReverse w) (x, (y : ℤ)))).card := by
      refine Finset.card_bij (fun x _ => (N_odd m : ℤ) - x) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, R, L, Finset.mem_Icc] at hx ⊢
        rw [isCovered_permReverse]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        unfold ptFlipX; simpa using hx.2
      · intro _ _ _ _ h; omega
      · intro x hx
        simp only [Finset.mem_filter, L, Finset.mem_Icc] at hx
        rw [isCovered_permReverse] at hx
        refine ⟨(N_odd m : ℤ) - x, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩, ?_⟩
        · exact hx.2
        · ring
    rw [hbij]
    simpa [L] using corner_row_holes_00 hm (isValidPerm_permReverse hw) (y := (y : ℤ))
      (by omega) (by omega)
  rw [hsplit, Finset.card_union_of_disjoint hd2', Finset.card_union_of_disjoint hd1',
    hL, hR] at htot
  have hs_id : (m + 1 - y) ^ 2 - 1 = (m - y) ^ 2 + 2 * (m - y) := by
    have hsub : m + 1 - y = (m - y) + 1 := by omega
    rw [hsub]
    have hexp : ((m - y) + 1) ^ 2 = (m - y) ^ 2 + 2 * (m - y) + 1 := by ring
    omega
  omega

private theorem claim5_inductive_E {m : ℕ} (hm : 1 ≤ m) :
    ∀ y : ℕ, 1 ≤ y → y ≤ m →
      ∀ w : Equiv.Perm (Fin (n_odd m)), IsValidOdd m w →
        (centralSet m).filter (fun x => ¬ isCovered m w (x, (y : ℤ))) =
          (centralSet m).filter (fun x => isTopCol m hm w x ∧ (y : ℤ) + 1 ≤ overhang m hm w x) := by
  intro y
  induction y using Nat.strong_induction_on with
  | h y ih =>
    intro hy1 hym w hw
    have h2m := two_mul_m_le_n_odd hm
    have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
    have hE' : ∀ y' : ℕ, 1 ≤ y' → y' < y →
        (centralSet m).filter (fun x => ¬ isCovered m w (x, (N_odd m : ℤ) - (y' : ℤ))) =
          (centralSet m).filter (fun x => isBotCol m hm w x ∧ (y' : ℤ) + 1 ≤ overhang m hm w x) := by
      intro y' hy'1 hy'lt
      have ih_comp := ih y' hy'lt hy'1 (by omega) (permComplement w) (isValidPerm_permComplement hw)
      ext x
      have hx_eq := congrArg (fun S => x ∈ S) ih_comp
      simpa [Finset.mem_filter, isCovered_permComplement, ptFlipY,
        isTopCol_permComplement, overhang_permComplement] using hx_eq
    have hsub :
        (centralSet m).filter (fun x => ¬ isCovered m w (x, (y : ℤ))) ⊆
          (centralSet m).filter (fun x => isTopCol m hm w x ∧ (y : ℤ) + 1 ≤ overhang m hm w x) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      rcases hx with ⟨hxC, hnc⟩
      refine ⟨hxC, ?_⟩
      rcases central_mem_top_or_bot hm hw hxC with htop | hbot
      · refine ⟨htop, ?_⟩
        by_contra hle
        have hgy : overhang m hm w x ≤ (y : ℤ) := by omega
        let g : ℤ := overhang m hm w x
        have hg_b := overhang_bounds hm hw hxC
        let S : Finset ℤ := Finset.Icc 1 (g - 1)
        have hS_sub : S ⊆ holesInCol m w x := by
          intro y' hy'
          rw [Finset.mem_Icc] at hy'
          rw [mem_holesInCol]
          refine ⟨hy'.1, by omega, ?_⟩
          have hy'_lt : y'.toNat < y := by omega
          have hih := ih y'.toNat hy'_lt (by omega) (by omega) w hw
          have hmem : x ∈ (centralSet m).filter
              (fun u => isTopCol m hm w u ∧ ((y'.toNat : ℤ) + 1 ≤ overhang m hm w u)) := by
            rw [Finset.mem_filter]
            exact ⟨hxC, htop, by omega⟩
          rw [← hih, Finset.mem_filter] at hmem
          have heq : (y'.toNat : ℤ) = y' := by omega
          rw [heq] at hmem
          exact hmem.2
        have hnotin : (y : ℤ) ∉ S := by
          rw [Finset.mem_Icc]; omega
        have hsub2 : insert (y : ℤ) S ⊆ holesInCol m w x :=
          Finset.insert_subset_iff.mpr ⟨mem_holesInCol.mpr ⟨by omega, by omega, hnc⟩, hS_sub⟩
        have hcard_le := Finset.card_le_card hsub2
        rw [Finset.card_insert_of_notMem hnotin, Int.card_Icc] at hcard_le
        have hcol_card := holesInCol_card_central hm hw hxC
        omega
      · exfalso
        obtain ⟨t, ht⟩ := hbot
        have hgy := overhang_eq_of_mem_botSupport hm hw ht
        have hg_b := overhang_bounds hm hw hxC
        by_cases hbig : (y : ℤ) + 1 ≤ overhang m hm w x
        · -- (x, y) is covered by (botCol t, 1 + t)!
          apply hnc
          refine ⟨w.symm (botRowIdx m hm t), ?_⟩
          change taxicabDist (plotPoint w (w.symm (botRowIdx m hm t))) (x, (y : ℤ)) ≤ (m : ℤ)
          have hpt : plotPoint w (w.symm (botRowIdx m hm t)) =
              (botCol m hm w t, 1 + (t.val : ℤ)) := by
            unfold plotPoint botCol
            rw [Equiv.apply_symm_apply]
            unfold botRowIdx
            dsimp only
            ring_nf
          rw [hpt]
          unfold taxicabDist
          dsimp only
          have h_abs_x : |botCol m hm w t - x| = (m : ℤ) - (t.val : ℤ) - overhang m hm w x := by
            rw [abs_sub_comm, hgy]; unfold tentHeight; ring
          rw [h_abs_x]
          rcases le_or_gt (1 + (t.val : ℤ)) (y : ℤ) with hy_ge | hy_lt
          · rw [abs_of_nonpos (by omega)]
            omega
          · rw [abs_of_pos (by omega)]
            omega
        · have hgy_le : overhang m hm w x ≤ (y : ℤ) := by omega
          let g : ℤ := overhang m hm w x
          let S : Finset ℤ := (Finset.Icc 1 (g - 1)).image (fun y' => (N_odd m : ℤ) - y')
          have hS_sub : S ⊆ holesInCol m w x := by
            intro z hz
            rw [Finset.mem_image] at hz
            obtain ⟨y', hy', rfl⟩ := hz
            rw [Finset.mem_Icc] at hy'
            rw [mem_holesInCol]
            refine ⟨by omega, by omega, ?_⟩
            have hy'_lt : y'.toNat < y := by omega
            have hE := hE' y'.toNat (by omega) hy'_lt
            have hmem : x ∈ (centralSet m).filter
                (fun u => isBotCol m hm w u ∧ ((y'.toNat : ℤ) + 1 ≤ overhang m hm w u)) := by
              rw [Finset.mem_filter]
              exact ⟨hxC, ⟨t, ht⟩, by omega⟩
            rw [← hE, Finset.mem_filter] at hmem
            have heq : (y'.toNat : ℤ) = y' := by omega
            rw [heq] at hmem
            exact hmem.2
          have hnotin : (y : ℤ) ∉ S := by
            rw [Finset.mem_image]
            rintro ⟨y', hy', hy_eq⟩
            rw [Finset.mem_Icc] at hy'
            omega
          have hsub2 : insert (y : ℤ) S ⊆ holesInCol m w x :=
            Finset.insert_subset_iff.mpr ⟨mem_holesInCol.mpr ⟨by omega, by omega, hnc⟩, hS_sub⟩
          have hcard_le := Finset.card_le_card hsub2
          rw [Finset.card_insert_of_notMem hnotin,
            Finset.card_image_of_injective _ (fun a b h => by omega), Int.card_Icc] at hcard_le
          have hcol_card := holesInCol_card_central hm hw hxC
          omega
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [row_central_holes_card hm hw hy1 hym, central_top_overhang_count hm hw hy1 hym]

/-- **Claim 5 (central columns):** For `x ∈ C` with overhang `g = overhang m hm w x`:
- if `x` is of top type, `holesInCol m w x = Finset.Icc 1 (g - 1)`;
- if `x` is of bottom type, `holesInCol m w x = Finset.Icc (N - (g - 1)) n`. -/
theorem claim5_central_col_holes {m : ℕ} (hm : 1 ≤ m) {w : Equiv.Perm (Fin (n_odd m))}
    (hw : IsValidOdd m w) {x : ℤ} (hx : x ∈ centralSet m) :
    (isTopCol m hm w x → holesInCol m w x = Finset.Icc 1 (overhang m hm w x - 1)) ∧
    (isBotCol m hm w x →
      holesInCol m w x = Finset.Icc ((N_odd m : ℤ) - (overhang m hm w x - 1)) (n_odd m : ℤ)) := by
  have hov := overhang_bounds hm hw hx
  have hcol_card := holesInCol_card_central hm hw hx
  have h2m := two_mul_m_le_n_odd hm
  have hN : (N_odd m : ℤ) = (n_odd m : ℤ) + 1 := by exact_mod_cast (n_odd_add_one m).symm
  constructor
  · intro htop
    have hsub : Finset.Icc 1 (overhang m hm w x - 1) ⊆ holesInCol m w x := by
      intro y hy
      rw [Finset.mem_Icc] at hy
      rw [mem_holesInCol]
      refine ⟨hy.1, by omega, ?_⟩
      have hE := claim5_inductive_E hm y.toNat (by omega) (by omega) w hw
      have hmem : x ∈ (centralSet m).filter
          (fun u => isTopCol m hm w u ∧ ((y.toNat : ℤ) + 1 ≤ overhang m hm w u)) := by
        rw [Finset.mem_filter]
        exact ⟨hx, htop, by omega⟩
      rw [← hE, Finset.mem_filter] at hmem
      have heq : (y.toNat : ℤ) = y := by omega
      rw [heq] at hmem
      exact hmem.2
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [Int.card_Icc]
    omega
  · intro hbot
    have hsub : Finset.Icc ((N_odd m : ℤ) - (overhang m hm w x - 1)) (n_odd m : ℤ) ⊆
        holesInCol m w x := by
      intro z hz
      rw [Finset.mem_Icc] at hz
      rw [mem_holesInCol]
      refine ⟨by omega, hz.2, ?_⟩
      let y := ((N_odd m : ℤ) - z).toNat
      have hy1 : 1 ≤ y := by omega
      have hym : y ≤ m := by omega
      have hE := claim5_inductive_E hm y hy1 hym (permComplement w) (isValidPerm_permComplement hw)
      have hmem : x ∈ (centralSet m).filter
          (fun u => isTopCol m hm (permComplement w) u ∧
            ((y : ℤ) + 1 ≤ overhang m hm (permComplement w) u)) := by
        rw [Finset.mem_filter, isTopCol_permComplement, overhang_permComplement]
        exact ⟨hx, hbot, by omega⟩
      rw [← hE, Finset.mem_filter, isCovered_permComplement] at hmem
      have hpt : ptFlipY (N_odd m : ℤ) (x, (y : ℤ)) = (x, z) := by
        unfold ptFlipY; ext <;> dsimp only; omega
      rw [hpt] at hmem
      exact hmem.2
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [Int.card_Icc]
    omega

end MinimalProlific
