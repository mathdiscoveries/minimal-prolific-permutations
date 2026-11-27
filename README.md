# Minimal `k`-Prolific Permutations for Every Odd `k` (`MinimalProlific`)

Lean 4 + Mathlib formalization of the companion paper's proof of **Conjecture 5.1 of Bevan, Homberger, and Tenner** (*J. Combin. Theory Ser. A* 153, 2018) for every odd $k = 2m - 1 \ge 1$ in its taxicab-breadth formulation, together with 2D radius-$m$ Lee-sphere tiling rigidity and the even-$k$ factorial lower bound.

- **Companion page & dated preprint (2026-11-23-v1):** [mathdiscoveries.org/results/minimal-prolific-permutations](https://mathdiscoveries.org/results/minimal-prolific-permutations)
- **Author / director:** Tyler B. Hughes (ORCID: [0000-0001-6221-9014](https://orcid.org/0000-0001-6221-9014))
- **Disclosure:** Generated and checked by AI research agents built and directed by Tyler B. Hughes. No human mathematician has yet refereed the proof.

## Headline Unconditional Theorems (`Challenge.lean`)

All five compared declarations in `Challenge.lean` are proved unconditionally in `Solution.lean` / `MinimalProlific/` using Lean 4 (`v4.35.0`) + Mathlib with **zero `sorry`**, **zero `native_decide`**, and **standard axioms only** (`propext`, `Quot.sound`, `Classical.choice`):

1. **`MinimalProlificChallenge.odd_minimal_prolific_classification`**: For every $m \ge 1$ (odd $k = 2m - 1$, minimal size $n = 2m^2 + 2m$, modulus $N = 2m^2 + 2m + 1$, breadth threshold $d = k + 2 = 2m + 1$), a permutation $w$ of $\{1, \ldots, n\}$ has breadth at least $d$ if and only if either $w(i) \equiv d\,i \pmod N$ for every $1 \le i \le n$, or $w(i) \equiv -d\,i \pmod N$ for every $1 \le i \le n$, with the sign fixed across all indices. (The Lean statement works on `Fin n` and shifts index and value by one.)
2. **`MinimalProlificChallenge.odd_minimal_prolific_card_eq_two`**: Exactly $2$ permutations of $\mathrm{Fin}(2m^2 + 2m)$ have taxicab breadth at least $2m + 1$.
3. **`MinimalProlificChallenge.odd_minimal_prolific_dihedral_orbit`**: Those two permutations are distinct, mutually related by reverse, complement, and inverse, and fixed by $90^\circ$ rotation (a single $D_4$ orbit of size $2$).
4. **`MinimalProlificChallenge.lee_tiling_classification`**: Every radius-$m$ Lee-sphere tiling $T \subseteq \mathbb{Z}^2$ containing $(0, 0)$ equals $\Lambda_+(m)$ or $\Lambda_-(m)$.
5. **`MinimalProlificChallenge.even_strip_lower_bound`**: For every $r \ge 2$ (even $k = 2r - 2$, minimal size $n = 2r^2 - 1$, breadth threshold $d = 2r$), at least $2(r - 1)! = 2(k/2)!$ permutations of $\mathrm{Fin}(2r^2 - 1)$ have taxicab breadth at least $2r$.

## Scope Boundary

This Lean 4 package proves the taxicab-breadth and Lee-sphere tiling theorems directly. Equivalence between $\text{breadth}(w) \ge k + 2$ and $k$-prolific permutations (and the minimal size $m(k) = \lceil k^2/2 + 2k + 1 \rceil$) is cited from Bevan, Homberger, and Tenner (*JCTA* 153, 2018, Theorem 2.25 and Corollary 4.3). The companion paper's even-$k$ torus-separated classification (Proposition 4) and exhaustive $k \le 8$ enumeration (Proposition 5) are outside this Lean package.

Coverage by this package's Palomar comparison: of the companion paper's 5 main results, 3 are compared in Lean in full (60%; Theorem 1 in its taxicab-breadth formulation, Theorem 2 and Lemma 3); Proposition 4 is by written proof only and Proposition 5 by certificate only; Conjecture 6 is open and not counted. Abstract claims: 3 of 3 compared in Lean (100%).

## Build & Verify

```sh
lake build MinimalProlific Challenge Solution
```

## License

Apache-2.0. See `LICENSE`.
