# Periodic Möbius rounding error — Lean 4 / Mathlib

This repository formalizes **exact periodic moments** of a truncated Möbius
rounding error and develops a route toward a genuinely stronger oscillation
theorem. The main research target is **open**; the verified finite identities
are structural reductions, not yet a new asymptotic result.

## Outstanding research question — not yet proved

For integers `B ≥ 2` and `M ≥ 0`, define

```text
E_B(M) = sum_{1 ≤ d ≤ B} mu(d) * ((M mod d) / d),
L_B = lcm(1, ..., B),
mean_B = (1/L_B) * sum_{0 ≤ M < L_B} E_B(M).
```

Does there exist a constant `C4 > 0`, independent of `B`, such that

```text
(1/L_B) * sum_{0 ≤ M < L_B} (E_B(M) - mean_B)^4 ≤ C4 * B^2
```

for all `B ≥ 2`? Establishing this bound could support quantitative
results about the frequency of large oscillations. **Neither the bound
nor those consequences have been proved, and no originality claim is made.**

## Main results actually verified in Lean

**Exact periodicity and centering.** Every positive common multiple
`T` of `1,...,B` is a period of `E_B`, and its mean is exactly

```text
E_B(M + T) = E_B(M),
mean_(B,T) = sum_{1 ≤ d ≤ B} mu(d) * (d - 1)/(2*d),
E_B(M) - mean_(B,T)
  = sum_{1 ≤ d ≤ B} mu(d) * ((M mod d)/d - (d - 1)/(2*d)).
```

In particular `T = B!` works. These statements have been proved for
arbitrary positive common periods, not only for a sample of integers.

**Second moment: reduction to pair correlations.** Define

```text
r_(d,H)(M) = (M mod d)/d
             - (1/H) * sum_{0 ≤ n < H} (n mod d)/d,
V_(B,H) = (1/H) * sum_{0 ≤ M < H} (E_B(M)-mean_(B,H))^2.
```

Lean proves that `V_(B,H)` is nonnegative and expands exactly into
the double sum of weighted pair correlations:

```text
V_(B,H) = (1/H) * sum_{0 ≤ M < H} sum_{1 ≤ a,b ≤ B}
  mu(a)*mu(b)*r_(a,H)(M)*r_(b,H)(M).
```

Equivalently, with

```text
C_(a,b;H) = (1/H) * sum_{0 ≤ M < H} r_(a,H)(M) * r_(b,H)(M),
```

Lean proves the exact quadratic-form identity

```text
V_(B,H) = sum_{1 ≤ a,b ≤ B} mu(a)*mu(b)*C_(a,b;H).
```

**This does not yet evaluate off-diagonal terms** `a ≠ b`.

The diagonal covariance for a complete modulus is also formalized:

```text
(1/d) * sum_{0 ≤ M < d} (M/d - (d-1)/(2*d))^2
   = (d^2 - 1)/(12*d^2)    (d ≥ 1).
```

**Fourth moment: exact correlation expansion.** The analogous
four-index expansion is verified in Lean. It reduces the problem to
four-way arithmetic correlations; it does **not** bound their total
contribution by `O(B^2)`.

See [FOURTH_MOMENT_RESEARCH.md](FOURTH_MOMENT_RESEARCH.md) for the
precise open problem, mathematical obstacles, and proof status.

## Supporting lemmas and the finite-sieve theorem

The file `FourthMomentResearch.lean` also proves the exact rational
remainder representation, mean over complete modular periods,
elementary uniform bounds, and the coarse fourth-moment bound

```text
|E_B(M)| ≤ B,
fourth_(B,H) ≤ 16*B^4    (H ≥ 1).
```

The `Challenge.lean` / `Solution.lean` pair has **one** submitted
Comparator theorem, `moebius_log_cutoff_residual_approximation`.
It links the periodic error to the omitted signed divisor mass of the
logarithmically truncated sieve: for `x ≥ 2`,
`B = 1+ceil((log x)^4)` and `M=ceil(x)-1`,

```text
|R(B,x) - 1 + M * sum_{1 ≤ d ≤ B} mu(d)/d| ≤ B.
```

This is a supporting **finite** approximation, not an asymptotic
cancellation theorem. It is not the claimed resolution of the open
fourth-moment question.

## Checking the proofs

`Challenge.lean` contains one **intentional** `sorry` for the challenge
statement. `Solution.lean` and `FourthMomentResearch.lean` contain
no `sorry`. The CI builds all three Lean modules; Comparator compares
the one Challenge/Solution theorem with Lean, NanoDa and con-ron.
The research lemmas are compiled by Lean, but are not separately listed
as Comparator challenge theorems.

```sh
lake exe cache get
lake build Challenge Solution FourthMomentResearch
bash scripts/check.sh
```

Running Comparator also requires `bwrap` and its independent kernels.

## Authorship and transparent AI assistance

**Author and responsible maintainer:** Alessandro Odasso.

ChatGPT **GPT-6 with High thinking effort** (as reported by the
contributor) assisted with mathematical exploration, proof drafting,
debugging, and repository verification. The project was human-directed
and AI-assisted. Formal verification establishes correctness of the
Lean statements actually proved; it does not establish mathematical
originality or replace independent mathematical review.

Project metadata: [formalization.yaml](formalization.yaml).
License: Apache-2.0.
