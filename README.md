# Möbius rounding error and logarithmically truncated sieve — Lean 4

A Lean 4/Mathlib development centered on a **finite rounding-error theorem**
and verified preliminary lemmas for a **fourth-moment research problem**.
The sharper fourth-moment conjecture remains unproved.

## Verified theorem

The public `Challenge.lean` / `Solution.lean` pair verifies the theorem:
`TruncatedSieveFlux.moebius_log_cutoff_residual_approximation`.

For `x ≥ 2`, put `B = 1 + ⌈(log x)^4⌉` and `M = ⌈x⌉ - 1`.
With lower threshold `A = 0`, upper cutoff `K(k) = k`, and omitted
signed Möbius mass `R(B,x)`, it proves the finite inequality

```text
|R(B,x) - 1 + M * sum_{1 ≤ d ≤ B} mu(d)/d| ≤ B.
```

This is an elementary bound on a *rounding discrepancy*, not an
asymptotic cancellation estimate for the Möbius function.

## Additional machine-checked research lemmas

The separate Lean module `FourthMomentResearch.lean` defines

```text
E_B(M) = M * sum_{1 ≤ d ≤ B} mu(d)/d
         - sum_{1 ≤ d ≤ B} mu(d) * floor(M/d)
       = sum_{1 ≤ d ≤ B} mu(d) * ((M mod d)/d).
```

For `H ≥ 1`, let `mean_(B,H)` be the average of `E_B(M)` on
`0 ≤ M < H`, and `fourth_(B,H)` the corresponding centered fourth
moment. The following statements have been proved in Lean:

```text
|E_B(M)| ≤ B
|mean_(B,H)| ≤ B
fourth_(B,H) ≤ (2B)^4 = 16B^4.
```

The exact modulo representation is also proved in Lean. These finite
facts set up the research question but are **not** a nontrivial
fourth-moment improvement: the `B^4` growth follows from the
pointwise error bound.

## Exact periodicity and fourth-order correlations

The research module also establishes that the fractional-part error is
periodic for every common multiple `T` of `1,...,B`:

```text
E_B(M + T) = E_B(M),    in particular T = B!.
```

For each `H`, write

```text
r_(d,H)(M) = (M mod d)/d - (1/H) * sum_{0 ≤ n < H} (n mod d)/d.
```

A proved exact decomposition isolates the correlations:

```text
E_B(M) - mean_(B,H) = sum_{1 ≤ d ≤ B} mu(d) * r_(d,H)(M).
```

Expanding the fourth power gives a proved, **finite fourfold formula**:

```text
fourth_(B,H) =
  (1/H) * sum_{0 ≤ M < H} sum_{a,b,c,d ≤ B}
    mu(a)*mu(b)*mu(c)*mu(d)
    * r_(a,H)(M)*r_(b,H)(M)*r_(c,H)(M)*r_(d,H)(M).
```

No bound on these four-way correlations beyond the elementary
`O(B^4)` estimate is established. That is the outstanding research task.

## Open research problem (NOT proved)

Write `L_B = lcm(1,...,B)` and `mean_B` for the average of `E_B`
over `0 ≤ M < L_B`. The proposed theorem asks whether an
absolute constant `C4 > 0` exists such that

```text
(1/L_B) * sum_{0 ≤ M < L_B} (E_B(M)-mean_B)^4 ≤ C4*B^2
```

for every `B ≥ 2`.

This **has not been proved**, and no mathematical novelty or
positive-density consequence is claimed. See
[FOURTH_MOMENT_RESEARCH.md](FOURTH_MOMENT_RESEARCH.md) for the
precise research status and obstacles.

## Verification

`Challenge.lean` has **one intentional** theorem `sorry`.
`Solution.lean` and `FourthMomentResearch.lean` have no `sorry`.

The CI builds all three modules. Comparator, with independent Lean,
NanoDa and con-ron kernels, compares the stated theorem
between Challenge and Solution. The additional fourth-moment lemmas
are checked by the normal Lean compiler, but are not registered as
separate Comparator challenges.

```sh
lake exe cache get
lake build Challenge Solution FourthMomentResearch
bash scripts/check.sh
```

Comparator also requires `bwrap` and the bundled independent kernels.

## Authorship and AI-use transparency

**Author and responsible maintainer:** Alessandro Odasso.

**AI disclosure:** ChatGPT **GPT-6 with High thinking effort**
(as reported by the contributor) was used in Lean proof drafting,
debugging, research exploration, and repository configuration.
Human-directed, AI-assisted work. Machine verification is not
independent mathematical peer review and does not establish novelty.

Metadata and source limitations are recorded in
[formalization.yaml](formalization.yaml). License: Apache-2.0.
