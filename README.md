# ω(F) ≤ 9/4 over every field, in Lean

This repository contains a Lean 4 proof that the matrix multiplication exponent of **every field**
is at most 9/4:

```lean
theorem OAI.MatrixMultiplication.omega_le_nine_quarters_all_fields (F : Type*) [Field F] :
    Arithmetic.omega F ≤ (9 : ℝ) / 4
```

(`OAI/LinearAlgebra/MatrixMultiplication/AllFields/Main.lean`.)

`Arithmetic.omega F` is the arithmetic exponent of square matrix multiplication over `F`. It is defined
in `OAI/LinearAlgebra/MatrixMultiplication/Model.lean`, verbatim as in the upstream comparator
challenge. The model is division-free straight-line programs over `F`: `constant` and `input` gates
cost 0, and `add`, `sub` and `mul` gates cost 1. `AdmissibleExponent F τ` means that for every ε > 0
one constant `C` bounds the cost of a correct program for n × n matrix multiplication by
`C · n^(τ+ε)` at every size n ≥ 1. `omega F` is the infimum of the admissible exponents.

The same file also proves the infimum-free form, so the statement is not vacuous:

```lean
theorem OAI.MatrixMultiplication.admissibleExponent_nine_quarters_all_fields (F : Type*) [Field F] :
    Arithmetic.AdmissibleExponent F ((9 : ℝ) / 4)
```

The admissible set is also bounded below by 2 (`Arithmetic.admissibleExponent_bddBelow`, upstream),
so `omega F` is a genuine infimum.

## Origin

This is a derived work of the Lean library in [openai/math](https://github.com/openai/math),
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/` (Apache-2.0). That library
formalises the result of the OpenAI paper below over ℂ: `omega ℂ ≤ 9/4`. This repository contains only
the 143 modules of that library that the all-fields theorem imports, with the same module names and
paths, so that a diff against upstream stays readable. Of these 143 modules:

- 99 are copied unchanged;
- 41 are modified, and each carries a header comment saying what was changed;
- 3 are new (`AllFields/Descent.lean`, `AllFields/Main.lean`, `AuxiliarySeparation/Tensor/MatMul.lean`).

[`NOTICE`](NOTICE) summarizes the changes; each modified source file has a detailed change header.
Upstream's other results (the α and rectangular bounds over ℂ, the all-fields bound
ω(F) < 2371054886006746/10¹⁵ (< 2.371056), and everything else in `openai/math`) are not included.

### Citation

The mathematics is that of

```bibtex
@misc{OAI:Matrix-Multiplication-Nine-Fourths-October-2-2026,
  author       = {{OpenAI}},
  title        = {{An Upper Bound of $9/4$ for the Matrix Multiplication Exponent}},
  howpublished = {OpenAI Math Release preprint \href{https://github.com/openai/math/blob/main/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/paper.pdf}{OAI:Matrix-Multiplication-Nine-Fourths-October-2-2026}},
  year         = {2026}
}
```

and the Lean formalisation over ℂ that this repository modifies is in
<https://github.com/openai/math> (commit `adc7f1241`, `lean/`).

## What was changed relative to upstream

The paper and the upstream formalisation work over ℂ. Only one step uses more of ℂ than "an
algebraically closed field": Proposition 3.1 (Fourier separation). It takes L = 5M copies and a
primitive 5M-th root of unity, which does not exist in characteristic p when p divides 5M; for p = 5
that is every M. The changes are as follows.

1. **Separation period.** Proposition 3.1 is proved for any period L with `(L : K) ≠ 0`,
   `L > 3(M − 1)` and a primitive L-th root of unity ζ ∈ K. The no-wrap argument needs only
   `L > 3(M − 1)`. For M ≥ 1 (the only case used; the period lemmas assume `M > 0`) the library
   takes `separationPeriod K M`, which is `3M − 2`, or `3M − 1` if `3M − 2` is zero in K. These are
   consecutive natural numbers, so one of the two is nonzero in K, and both are ≤ 5M. The bound
   `χ(target) ≤ 5M · χ(shared)` downstream is therefore unchanged. The primitive root is a root of the
   L-th cyclotomic polynomial, which exists because K is algebraically closed.
   (`AuxiliarySeparation/Separation/{Fourier,NoWrap,FiniteProjection,Basic}.lean`,
   `AuxiliarySeparation/Character/FiniteSeparation.lean`.)
2. **An arbitrary algebraically closed field K.** The proof in `AuxiliarySeparation/` is
   parameterized by a field `{K : Type} [Field K]` in place of ℂ; ℂ remains only in the explicit
   corollary `complex_omega_le_nine_quarters` (and in unchanged upstream helper modules).
   `[IsAlgClosed K]` is assumed only by the 35 declarations that use it: the interpolation nodes,
   the primitive roots of unity, and the results that depend on them. Interpolation and convolution
   nodes were `1, …, D+1` and `0, …, a+b−2` in ℂ. They are now the first values of an embedding of ℕ
   into K (or into K∖{0}), which needs only that K is infinite. The generalized argument needs no
   characteristic-zero (`CharZero`) hypothesis. Six ℂ-only lemmas, whose removal does not affect the
   retained proof, were deleted: border-rank and degeneration statements in `Separation/Basic`,
   `Convolution/Rank`, `Polynomial/Interpolation` and `Sector/Degeneration`.
   `AuxiliarySeparation.omega_le_nine_quarters : omega K ≤ 9/4` holds for every algebraically closed
   `K`, and the upstream ℂ statement is its instance `complex_omega_le_nine_quarters`.
3. **Arithmetic bridge over an arbitrary field.** `AuxiliarySeparation/Arithmetic/Exponent.lean` was
   rewritten. The rank-to-programs step now uses the library's field-generic block recursion
   (`Arithmetic.rectangularAdmissibleExponent_of_rankAtMost`) instead of a ℂ-only chain.
4. **Descent to every field** (new: `AllFields/Descent.lean`, `AllFields/Main.lean`). Let P be the
   prime field of F (ℚ or `ZMod p`) and K its algebraic closure. A decomposition of ⟨u,u,u⟩ over K of
   size r has its coefficients in a finite extension E/P, of degree m say. Taking the j-th tensor power
   over E and expanding the coefficients in a P-basis gives a decomposition of ⟨uʲ,uʲ,uʲ⟩ over P of size
   m³rʲ. Mapping P → F gives the same over F, and the factor m³ disappears as j → ∞.
5. **Clean-up.** Docstrings that said "complex" where they now mean `K` were corrected. A few
   linter warnings were fixed: `haveI` became `have`, unused `simp` arguments were removed, and an
   unused hypothesis was renamed `_hM`. `lake build` reports no warnings from this repository's
   files.

The module docstring of `AllFields/Main.lean` sketches the descent.

## Trust base

- **Axioms.** `#print axioms` for the main theorems reports only `propext`, `Classical.choice` and
  `Quot.sound` (see [`Checks/Axioms.lean`](Checks/Axioms.lean)). There is no `sorry` outside the
  comparator challenge file. That file's single `sorry` is the placeholder for the statement, which
  is what the comparator protocol requires.
- **Kernel.** The proof is checked by the Lean 4 (v4.34.1) default kernel, both in `lake build` and in
  the comparator's replay of the exported proof. No second kernel (nanoda, lean4lean) was run; the
  challenge config has `enable_nanoda: false`, as upstream.
- **Comparator.** [`leanprover/comparator`](https://github.com/leanprover/comparator) checks
  `ComparatorChallenges/MatrixMultiplicationAllFields.json`. That configuration has a single target,
  the final theorem `OAI.MatrixMultiplication.omega_le_nine_quarters_all_fields`; the corollaries
  (`admissibleExponent_nine_quarters_all_fields`, `matrix_multiplication_cost_le_all_fields`) are
  checked by `lake build` and have their own `#print axioms` queries, but are not comparator
  targets. The JSON's first property, `_modification_notice`, is the Apache-2.0 change notice;
  comparator ignores it. The challenge file
  `ComparatorChallenges/MatrixMultiplicationAllFields.lean` is a copy of upstream's
  `ComparatorChallenges/MatrixMultiplication.lean`. Its `namespace MatrixMultiplication.Arithmetic …
  end` block (all definitions of the model) is verbatim; only the header comment and the theorem
  statement differ. The challenge file is ours, not OpenAI's.
- **Dependencies.** Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612` (its build cache from
  `cache.mathlib.org`), and
  [fixed-point-theorems](https://github.com/harfe/fixed-point-theorems-lean4) at
  `770940ddf9878cf61952ed53d910b92bca841838` (for Brouwer's fixed-point theorem). The latter is patched
  for Lean v4.34.1 by upstream's `patches/fixed-point-theorems-lean4341.patch`, which `lake update`
  applies through the `post_update` hook in `lakefile.lean`. `lake-manifest.json` is generated by
  `lake update` and lists only this project's packages; each of its package entries (both direct
  pins and all transitive pins) is identical to the corresponding entry of upstream's manifest.

## Reproduction

Requirements: [elan](https://github.com/leanprover/elan), which installs the pinned toolchain
`leanprover/lean4:v4.34.1` from `lean-toolchain`, plus `git` and network access, and about 8 GB of
memory (the largest single process used 6.2 GiB in the recorded run, about 6.5 GB in an earlier
one). The comparator step also needs `comparator`, `lean4export` and `landrun` on `PATH` and a
Linux sandbox environment as described in the
[comparator README](https://github.com/leanprover/comparator). There are no v4.34.1 tags of
`comparator` and `lean4export`: check out their `v4.34.0` tags, set their `lean-toolchain` to
`leanprover/lean4:v4.34.1`, run `lake build`, and put each checkout's `.lake/build/bin/` on `PATH`.
`landrun` is a Go program: see [Zouuup/landrun](https://github.com/Zouuup/landrun).

```sh
git clone https://github.com/jzuiddam/omega-nine-quarters-all-fields.git
cd omega-nine-quarters-all-fields
lake update        # fetches dependencies, applies the fixed-point-theorems patch, fetches the Mathlib cache
lake exe cache get
lake build
lake build ComparatorChallenges.MatrixMultiplicationAllFields
lake env lean Checks/Axioms.lean
lake env comparator ComparatorChallenges/MatrixMultiplicationAllFields.json
```

`lake update` is required, as it is upstream: the compatibility patch for fixed-point-theorems is
applied only in the `post_update` hook. Without the patch that dependency does not compile with
Lean v4.34.1. `lake update` leaves `lake-manifest.json` unchanged (checked with `git diff`). It
prints `warning: toolchain not updated; multiple toolchain candidates` (this project's v4.34.1 and
fixed-point-theorems' v4.32.0). The warning is harmless: `fixedToolchain := true` in `lakefile.lean`
keeps v4.34.1.

**Continuous integration.** [`.github/workflows/build.yml`](.github/workflows/build.yml) runs the
first five commands on every push and pull request to `main`, fails if `lake update` changes
`lake-manifest.json`, and fails unless every `#print axioms` in `Checks/Axioms.lean` reports only
`propext`, `Classical.choice` and `Quot.sound` ([`.github/check_axioms.py`](.github/check_axioms.py)).
The comparator is not part of it; a separate, manually triggered and experimental workflow
([`comparator-manual.yml`](.github/workflows/comparator-manual.yml)) tries it, but `landrun` may not
work on GitHub-hosted runners. Hosted runners for private repositories (2 cores, 7 GB) may be too
small for the single-process peak of about 6.5 GB, although the first run there (commit `c130a99`)
passed in 12 minutes; CI is expected to be reliable once the repository is public (4 cores, 16 GB).

### Verification record

The commands above were run on a fresh clone of commit `c130a996c754b8407d92a4518db9711f4105260d`.
That is the last commit to change anything other than this README.

- **Where.** Slurm job 37025 (16 CPUs, `--mem=64G`, `LEAN_NUM_THREADS=16`) on a Debian 12 node
  (kernel 6.12) of the Berkeley OCF cluster, on 2026-10-07 (PDT).
- **Fresh state.**
  - `.lake` was a new empty directory, linked as `.lake -> /var/tmp/...`;
  - `MATHLIB_CACHE_DIR` pointed to a new empty directory, so the Mathlib cache was downloaded
    afresh;
  - `CURL_CA_BUNDLE=/etc/ssl/certs/ca-certificates.crt` was set;
  - every step was run under `/usr/bin/time -v`.
- **Tools** (as installed on 2026-10-07). `comparator` at tag `v4.34.0`
  (`d03acab154d269c06e60e4de7e4cc85deebff94b`) and `lean4export` at tag `v4.34.0`
  (`076e8e57707e813375e8f9da8bf989799ace9680`), each built with `lean-toolchain` set to
  `leanprover/lean4:v4.34.1`; `landrun` 0.1.18; elan 4.1.2.

The memory column is the maximum resident set size of the largest single process of that step
(from `/usr/bin/time -v`), not the total memory in use: Lean's parallel build runs many processes at
once, and Slurm recorded 28.8 GiB as the batch step's MaxRSS over the whole job.

| step | wall time | max RSS (one process) | result |
|---|---|---|---|
| `git clone` | 0:01 | | |
| `lake update` | 1:32 | 0.8 GiB | patch applied ("applied compatibility patch fixed-point-theorems-lean4341.patch"); 8,908 Mathlib cache files downloaded by Mathlib's own update hook; manifest unchanged; the harmless multiple-toolchain warning |
| `lake exe cache get` | 0:05 | 0.5 GiB | "No files to download" |
| `lake build` | 1:12 | 6.2 GiB | "Build completed successfully (9074 jobs)"; no `sorry`; the only warning is Lake's note that the patched dependency has local changes |
| `lake build ComparatorChallenges.MatrixMultiplicationAllFields` | 0:08 | 6.1 GiB | "Build completed successfully (8924 jobs)"; one `declaration uses 'sorry'`, which is the challenge placeholder |
| `lake env lean Checks/Axioms.lean` | 0:05 | 6.1 GiB | all five `#print axioms`: `[propext, Classical.choice, Quot.sound]` (also checked by `.github/check_axioms.py`); the `#check`s show `(F : Type u_1)` |
| `lake env comparator ComparatorChallenges/MatrixMultiplicationAllFields.json` | 1:55 | 6.2 GiB | "Lean default kernel accepts the solution", "Your solution is okay!", exit 0 (the configuration includes the `_modification_notice` key) |

The whole job took 4:58 wall. The SHA-256 sums of the challenge `.lean`/`.json`, `lakefile.lean`,
`lake-manifest.json` and `lean-toolchain` were the same before `lake update` and after the
comparator run, and `git status` was clean at the end (the `.lake` symlink is ignored). An
earlier run on commit `04378a5` (before the publication fixes) gave the same results, with a largest
single process of about 6.5 GB.

## Caveats

- The comparator was run with the same compromises as in our earlier audit of upstream:
  - comparator v4.34.0 always invokes `landrun` with `--best-effort`; the node's Landlock ABI is v6,
    so the sandbox ran with reduced capabilities;
  - the documented `systemd-run --user` wrapper was not available (there is no user systemd bus in a
    Slurm job);
  - the solution had been built with `lake build` before the comparator ran, contrary to the
    comparator's assumption that the solution has not been compiled before. The comparator's own
    rebuild was therefore a cache replay.

  The recorded run replayed the export in Lean's default kernel. Because of these compromises, it
  is not evidence that all of comparator's adversarial-isolation assumptions were met.
- `comparator` and `lean4export` were built from their `v4.34.0` tags with `lean-toolchain` set to
  v4.34.1, since no v4.34.1 tags exist.
- Internal statements of the library changed: six ℂ-only lemmas that the retained proof does not
  need were deleted, and `interpolationNode` is no longer `1, …, D+1`. Only the final theorem
  `omega_le_nine_quarters_all_fields` is checked against a challenge file.
- This repository checks that the stated theorem is proved. Whether the arithmetic model captures the
  intended notion of ω is a matter of reading `Model.lean` (or the challenge file).

## Authorship and licence

Modifications and new files: Jeroen Zuiddam, 2026. Developed with AI assistance (Claude); verified by
the Lean kernel and the comparator. The upstream library is by OpenAI. Licensed under the Apache
License 2.0 ([`LICENSE`](LICENSE)); see [`NOTICE`](NOTICE).
