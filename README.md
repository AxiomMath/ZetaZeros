[![](logo.svg)](https://axiommath.ai/)

# Simple zeros of the Riemann zeta function on the critical line

This is a Lean formalization of Lamzouri's new proof that more than `2/3` of the zeros of the Riemann zeta function are simple and on the critical line.

## Main Results

* A Hilbert-space lower bound on the number of real points of multiplicity one in a finite conjugation-invariant multiset, and on the number of its distinct points.
* Beyond some height, more than `67.25%` of the non-trivial zeros are simple and lie on the critical line, assuming the Riemann–von Mangoldt formula, the Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh pair-correlation formula and the Montgomery–Taylor computation.
* Beyond some height, more than `83.625%` of the non-trivial zeros are distinct, under those same three assumptions.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results
claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only
depends on the dependency above. It contains formal statements of
[§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean
comparator on a Linux machine. First, follow the instructions in
https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:

```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
