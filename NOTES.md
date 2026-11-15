# Notes: what is proved and how it was checked (15 November 2026)

## What is proved

Everything below is proved in Lean 4 (v4.35.0, Mathlib v4.35.0) with no `sorry`, no `native_decide`
and only the axioms `propext`, `Classical.choice` and `Quot.sound`. The statements of record are in
`Challenge.lean`; `comparator.json` names the four compared theorems.

- `Gw444.exists_good`: for `4 ≤ r ≤ 6`, a good exact `r`-colouring of `[1, 328]` for rainbow 4-term
  and monochromatic 4-term progressions.
- `Gw444.lt_of_gwProperty`: for `4 ≤ r ≤ 6`, every `M` with `GWProperty r 4 4 M` exceeds 328.
- `Gw444.lt_GW`: for `4 ≤ r ≤ 6`, `328 < GW r 4 4` if some threshold exists.
- `Gw444.exists_canonical`: a colouring `ℕ → ℕ` of `[1, 328]` with no rainbow and no monochromatic
  4-term progression (`H(4) ≥ 329`).

The colourings rest on 24 kernel checks by `decide +kernel`: for each of the three colourings,
`allCols` (every colour occurs) and `rangeTest` on seven pieces of the range of differences
`1 ≤ d ≤ 109` (at most 3,000 start points each). `good_of_tests` (proved for every input) turns them
into `IsGoodExactColouring`. `scripts/make_colourings.py` built the colourings from the cubic residue
classes modulo 109, checked them by brute force (no bad progression; every colour used; class sizes
110, 108, 108, 2 / 108, 108, 108, 2, 2 / 108, 108, 108, 2, 1, 1) and found the 4-colouring equal, up
to the names of the colours, to `gw/colouring_1_328.txt` of the public data repository; the Lean
proof relies on none of this.

## Line counts

| File | Lines |
|---|---|
| `Challenge.lean` | 94 (5,460 bytes) |
| `Solution.lean` | 51 |
| `Gw444.lean` | 5 |
| `Gw444/Defs.lean` | 40 |
| `Gw444/Check.lean` | 236 |
| `Gw444/Colourings.lean` | 163 (generated) |
| `scripts/CheckAxioms.lean` | 16 |

Every `.lean` file starts with `module`; `Challenge.lean` imports only Mathlib
(`Mathlib.Order.Lattice.Nat`).

## Checks run (Mac, Apple silicon, Lean v4.35.0)

All on a fresh clone of commit `c49b64b5bb3b1175f224aed59c7f2e18cb2cd492` (the commit before this
file was added; no Lean file changed since), with the Lake packages of the pinned Mathlib checkout and
the project's own modules built from scratch (a local check script; its log is kept outside this
repository).

1. `lake build`: every module built in 28 s; `Gw444.Colourings` (the kernel checks) 12 s.
   `Challenge` warns four times (declaration uses `sorry`, as intended).
2. `lake env lean scripts/CheckAxioms.lean`: `[propext, Quot.sound]` or
   `[propext, Classical.choice, Quot.sound]` for each of the four theorems.
3. `lake comparator` needs bubblewrap (Linux namespaces) and does not run on macOS. In its place,
   steps 4 and 6 were run by hand.
4. Statement comparison: every constant reachable from the types of the compared theorems (following
   definition values, not proofs) was printed with `pp.all` and hashes in the Challenge and in the
   Solution environment. Apart from the module of the three own definitions (`Challenge` against
   `Gw444.Defs`), the two outputs (4 roots, 120 constants) are identical.
5. Red controls (`RedControl.lean`): the 4-colouring with point 2 recoloured (five bad progressions),
   the 4-colouring tested for rainbow 3-term progressions, the 4-colouring on `[1, 329]`, the
   5-colouring read with 4 colours, and a missing fifth colour of the 4-colouring are all rejected by
   the kernel; the 6-colouring over all differences at once and its colour test pass.
6. Kernel replays: `leanexport` wrote both modules with the compared theorems as targets; the Solution
   export (5.5 MB) was replayed through every kernel bundled with the toolchain (each run would have
   been stopped had it passed 7 GB of memory; none did):

   ```
   leanchecker            rc 0    17 s
   nanoda                 rc 0     4 s   0.6 GB
   con-ron                rc 0     2 s   accepted 1740 declarations (--verified)
   leanchecker-paranoid   rc 0    22 s
   lean4lean              rc 0    20 s   checked 1737 declarations
   con-leche              rc 0     4 s   3.1 GB   accepted 1740 declarations (--verified)
   ```

   NanoDa with unpermitted axioms as a hard error: Solution export exit 0; Challenge export exit 1
   (`export file declares unpermitted axiom "sorryAx"`), as it should. `Lean.ofReduceBool` does not
   occur in the Solution export. SHA-256 of the exports: `solution.ndjson`
   `c57b404e2c36df2ced308965316472b59bfd7dfe152a2892e05b129242808303`, `challenge.ndjson`
   `673eaf3b3e3bf43ac89b9291cefa88b0d291fa7e5263146004ba853938d61079`.

An earlier version of the check (one `decide +kernel` per colouring over all pairs `x, d ≤ 328` with
`List` loops) also built and replayed in Lean's kernel, but NanoDa, con-ron and con-leche passed 7 GB
of memory on it; the present version replaces it.

## What remains

- Palomar's mechanical preflight (the workflow above, on GitHub's Linux runners) has not run: it needs
  the repository to be public on GitHub.
- No review outside Quantavane's agents.
- Not formalized: the Gallai–van der Waerden theorem (existence of a threshold), the general residue
  constructions, any upper bound for `GW(r; 4, 4)`.
