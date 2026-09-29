# Lean formalization of OPAC-012

This directory contains a Lean 4 / mathlib formalization of the proof of
[OPAC-012](https://realopacblog.wordpress.com/), concerning a positivity
conjecture of Lewis and Morales.

The corresponding mathematical proof is contained in
[`../solution/opac012-solution.pdf`](../solution/opac012-solution.pdf).
The main repository also contains supplementary computations and a record
of the process by which the solution was obtained.

## Status

The proof of the main result has been completely formalized in Lean.

The formalization is intended to verify the mathematical argument in the
paper, rather than to provide a maximally general-purpose library for its
constituent combinatorial identities. Some definitions and lemmas are
therefore specialized to the OPAC-012 argument.

The formal endpoint of the development is in
[`OPAC012/Main.lean`](OPAC012/Main.lean).

## Mathematical structure

The paper proves positivity by passing through three main stages.

Writing \(S_{k,m}\) for the polynomial appearing in the conjecture, one
first normalizes the problem to a family \(F_t(a)\), with

\[
S_{k,m}=[m-k]!\,F_k(m-k).
\]

One then establishes a universal expansion of \(F_t(a)\) in terms of
Gaussian binomial coefficients and polynomials \(\Theta_{t,j}(q)\).
The dependence on \(a\) is carried by the Gaussian-binomial factors, while
the \(\Theta_{t,j}\) are universal.

Finally, the coefficients \(\Theta_{t,j}\) are proved to be nonnegative.
The key step is a coefficientwise domination argument, ultimately reduced
to an elementary convexity inequality for ordinary binomial coefficients.

Thus the main logical spine of both the paper and the formalization is

\[
S \longrightarrow F \longrightarrow \Theta
\longrightarrow \text{coefficientwise positivity}.
\]

## Organization

The source files are divided according to the main pieces of the proof.

| File | Role |
| --- | --- |
| [`Basic.lean`](OPAC012/Basic.lean) | Basic definitions and preliminary lemmas |
| [`QFactorial.lean`](OPAC012/QFactorial.lean) | \(q\)-integers, \(q\)-factorials, and related identities used in the proof |
| [`Normalization.lean`](OPAC012/Normalization.lean) | Reduction from the original OPAC-012 polynomial \(S_{k,m}\) to the normalized family \(F_t(a)\) |
| [`UniversalExpansion.lean`](OPAC012/UniversalExpansion.lean) | Universal Gaussian-binomial expansion and the coefficients \(\Theta_{t,j}\) |
| [`Domination.lean`](OPAC012/Domination.lean) | Coefficientwise domination argument establishing positivity of the universal coefficients |
| [`Sharpness.lean`](OPAC012/Sharpness.lean) | Formalization of the sharpness/boundary statements accompanying the main theorem |
| [`Main.lean`](OPAC012/Main.lean) | Assembly of the preceding results and proof of the main theorem |

[`OPAC012.lean`](OPAC012.lean) imports the complete development and is
provided as a convenient single entry point.

## Building the formalization

The project pins its Lean version in `lean-toolchain` and its mathlib
dependencies in `lake-manifest.json`.

Starting from the root of this repository:

```bash
cd lean
lake exe cache get
lake build
```

A successful `lake build` checks the entire formalization using the pinned
Lean and mathlib versions.

No separate system-wide installation of mathlib is required. A working
Lean installation through `elan` is sufficient; Lake will use the
toolchain specified by this project.

## Verification

Lean's kernel checks every theorem in the development from the stated
axioms and imported library results.

The formalization contains no intentional placeholders (`sorry`) in the
proof of the main result.

For a reproducibility check, clone the repository and run

```bash
cd lean
lake exe cache get
lake build
```

The GitHub Actions workflow in

```text
../.github/workflows/lean.yml
```

performs the same build in a clean environment.

For the archived release accompanying the paper, the relevant git tag
should be regarded as the canonical version of the formalization.

## Relationship with the paper

The Lean development follows the proof given in the paper fairly closely,
but the correspondence is not line-by-line. Lean requires a number of
algebraic identities, boundary cases, coercion lemmas, and polynomial
manipulations that are implicit in the mathematical exposition.

At the structural level, the correspondence is:

| Paper | Lean |
| --- | --- |
| Preliminary \(q\)-identities | `Basic.lean`, `QFactorial.lean` |
| Normalization \(S_{k,m}=[m-k]!\,F_k(m-k)\) | `Normalization.lean` |
| Universal expansion of \(F_t(a)\) | `UniversalExpansion.lean` |
| Positivity of \(\Theta_{t,j}\) by coefficientwise domination | `Domination.lean` |
| Main positivity theorem | `Main.lean` |
| Sharpness statements | `Sharpness.lean` |

The formalization is therefore best viewed as a machine-checked
counterpart of the proof, rather than as an independent proof with a
different mathematical strategy.

## AI-assisted formalization

This formalization was produced with substantial assistance from large
language models in an interactive autoformalization workflow.  (This README 
likewise was drafted by an LLM.)

The mathematical theorem and its proof are described independently in the
paper. The generated Lean code was developed iteratively against Lean and
mathlib until the complete development was accepted by the Lean kernel.

Kernel acceptance establishes that the Lean theorem follows from the
definitions, imported results, and axioms appearing in the formal
development. As with any formalization, the identification of the formal
statement with the intended informal mathematical statement is a matter
of human-readable specification and review; the tables and documentation
above are intended to make that correspondence transparent.

Further provenance information is recorded in `formalization.yaml`.

