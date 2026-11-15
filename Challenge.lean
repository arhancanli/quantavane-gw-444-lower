module

public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Lower bounds for the diagonal Gallai–van der Waerden numbers `GW(r; 4, 4)`: the statement

This file is the statement of record. It imports only Mathlib, defines the notions the statements
use, and states the results with `sorry`. `Solution.lean` proves every statement; `comparator.json`
names the compared theorems. The definitions below must agree exactly with the ones the proof uses
(Comparator checks this), so they are spelled out here in full.

## Gallai–van der Waerden numbers

Write `[1, n] = {1, …, n}`. An *exact `r`-colouring* of `[1, n]` is a colouring of `[1, n]` with
`r` colours in which every colour occurs. An arithmetic progression (AP) always has common
difference `d ≥ 1`. A `k`-term AP `x, x + d, …, x + (k - 1)d` is *rainbow* when its `k` terms have
pairwise distinct colours, and an `l`-term AP is *monochromatic* when all its terms have the same
colour. The Gallai–van der Waerden number `GW(r; k, l)` of Mao, Ozeki, Robertson and Wang
(J. Combin. Theory Ser. A 193 (2023) 105672, Definition 1.15) is the least `M` such that, for every
`n ≥ M`, every exact `r`-colouring of `[1, n]` contains a rainbow `k`-term AP or a monochromatic
`l`-term AP. The definitions below are those of the registered entry PALOMAR-2026-11-12-000009
(`GwPower`, Gallai–van der Waerden numbers from `m`-th power residue colourings).

## The results (Quantavane, November 2026)

* `exists_good`: for `r = 4, 5, 6`, the interval `[1, 328]` has an exact `r`-colouring with no
  rainbow 4-term AP and no monochromatic 4-term AP.
* `lt_of_gwProperty`, `lt_GW`: hence `GW(r; 4, 4) ≥ 329 = 3 · 109 + 2` for `r = 4, 5, 6`.
* `exists_canonical`: some colouring of `[1, 328]`, with any number of colours, has neither a
  rainbow 4-term AP nor a monochromatic 4-term AP; that is, the canonical number `H(4) = H(4, 4)`
  (the least `n` such that every colouring of `[1, n]` has one of the two) is at least `329`.

The case `r = 6` is also an instance of PALOMAR-2026-11-12-000009 (`GW(6; 4, 4) > 328`), and the
same entry gives `GW(4; 4, 4) > 327`. Before these, the best published lower bound for
`GW(4; 4, 4)` was `186` (Y. Si, arXiv:2610.30711). The colourings are explicit; they agree with a
cubic-residue colouring modulo the prime `109` off the four points `1, 110, 219, 328`.
-/

namespace Gw444

/-- `c` is a *good exact `r`-colouring of `[1, n]`* for rainbow `k`-term and monochromatic `l`-term
arithmetic progressions: every colour `col : Fin r` occurs on `[1, n]`; no `x, x + d, …, x + (k - 1)d`
in `[1, n]` with `d ≥ 1` has `k` pairwise distinct colours; and no `x, x + d, …, x + (l - 1)d` in
`[1, n]` with `d ≥ 1` has all its terms of one colour. The colouring is a function on all of `ℕ`;
its values outside `[1, n]` play no role. -/
def IsGoodExactColouring (r k l n : ℕ) (c : ℕ → Fin r) : Prop :=
  (∀ col : Fin r, ∃ x, 1 ≤ x ∧ x ≤ n ∧ c x = col) ∧
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (k - 1) * d ≤ n →
    ¬ ∀ i < k, ∀ j < k, i ≠ j → c (x + i * d) ≠ c (x + j * d)) ∧
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ n → ¬ ∀ j < l, c (x + j * d) = c x)

/-- `M` has the defining property of the Gallai–van der Waerden number `GW(r; k, l)`
(Mao–Ozeki–Robertson–Wang, JCTA 2023, Def. 1.15): for every `n ≥ M`, every exact `r`-colouring of
`[1, n]` contains a rainbow `k`-term AP or a monochromatic `l`-term AP, that is, no `[1, n]` with
`n ≥ M` has a good exact `r`-colouring. -/
def GWProperty (r k l M : ℕ) : Prop :=
  ∀ n ≥ M, ∀ c : ℕ → Fin r, ¬ IsGoodExactColouring r k l n c

/-- `GW(r; k, l)`: the least `M` with `GWProperty r k l M`. Lean's `sInf` of the empty set of
natural numbers is `0`; the Gallai–van der Waerden theorem says that the set is not empty, but it is
not formalised here, so `lt_GW` assumes that some `M` has the property. -/
noncomputable def GW (r k l : ℕ) : ℕ := sInf {M | GWProperty r k l M}

/-- **Good exact colourings of `[1, 328]`.** For `r = 4, 5, 6` there is an exact `r`-colouring of
`[1, 328]` with no rainbow 4-term AP and no monochromatic 4-term AP. -/
theorem exists_good (r : ℕ) (h4 : 4 ≤ r) (h6 : r ≤ 6) :
    ∃ c : ℕ → Fin r, IsGoodExactColouring r 4 4 328 c := by
  sorry

/-- **`GW(r; 4, 4) ≥ 329` for `r = 4, 5, 6`** (threshold form). Every `M` with the defining property
of `GW(r; 4, 4)` exceeds `328`. This form needs no assumption that such an `M` exists. -/
theorem lt_of_gwProperty (r : ℕ) (h4 : 4 ≤ r) (h6 : r ≤ 6) (M : ℕ) (hM : GWProperty r 4 4 M) :
    328 < M := by
  sorry

/-- **`GW(r; 4, 4) ≥ 329` for `r = 4, 5, 6`**, for the number itself, given that some `M` has the
property (`hex`, the Gallai–van der Waerden theorem, not formalised here). -/
theorem lt_GW (r : ℕ) (h4 : 4 ≤ r) (h6 : r ≤ 6) (hex : ∃ M, GWProperty r 4 4 M) :
    328 < GW r 4 4 := by
  sorry

/-- **`H(4) ≥ 329`.** Some colouring of `[1, 328]` (by natural numbers, with any number of colours)
has no rainbow 4-term AP and no monochromatic 4-term AP. -/
theorem exists_canonical :
    ∃ c : ℕ → ℕ,
      (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 3 * d ≤ 328 →
        ¬ ∀ i < 4, ∀ j < 4, i ≠ j → c (x + i * d) ≠ c (x + j * d)) ∧
      (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 3 * d ≤ 328 → ¬ ∀ j < 4, c (x + j * d) = c x) := by
  sorry

end Gw444
