# One common sample for all semantic C1 columns

Continuation from `f021007879dcd9e2bca795b4758e187fa1c3b302`.
This consumes the completed Gao and circle-polynomial proofs; it changes no
protocol, verifier operation or proof byte.

## New deterministic implication

[`CommonFibreGaoRecovery.lean`](experiments/CommonFibreGaoRecovery.lean) proves:

> Given the same 513 complete-fibre sample for all 16 semantic C1 columns,
> if at most 128 sampled fibres are bad, every column decoder returns its
> coefficients of the qualifying code tuple, under the explicit circle/encoder/inverse
> interfaces of `GaoC1Recovery`.

The received samples may be arbitrary non-polynomial values, including
totalized values from noncanonical raw committed bytes. There is no assumed
decoder success, honest received word, provider return or payment witness.

The flattening is literally `4*fibre+slot`. Each erroneous scalar index lies
in the mapped product of the common bad-fibre set with four slots. Thus each
column has at most four times the common number of bad fibres in error.
The ambient scaled circle polynomial has dimension 1025. With 2052 scalar
samples its unique-decoding radius is `floor((2052-1025)/2)=513`.
At most 128 bad fibres supplies at most 512 errors, so the existing finite-fuel
Euclidean decoder theorem applies to every column simultaneously.

`selected_failure_requires_129` is the contrapositive: failure to return the
whole semantic coefficient tuple requires at least 129 bad sampled fibres,
subject to those deterministic interfaces. The number of columns introduces
**no factor of 16** into the sampling failure event. This is stronger than
sixteen unrelated per-column decoder claims with separate bad supports.

## What is reused and what is still required

| Interface | Status |
|---|---|
| Common-fibre errors to all-column Gao success | New kernel-checked theorem |
| Finite-fuel Euclidean decoder on arbitrary received values | Reused `GaoRecovery.decoder_complete` |
| Natural tensor to one fixed degree-at-most-1024 polynomial | Reused `CircleLaurentRecovery.natural_tensor_embedding` |
| Polynomial recovery to coefficient vector | Reused `GaoC1Recovery.recover_coefficients` |
| Exact point/circle/source encoder and public matrix inverse | Explicit premises; earlier optimized Rust checks are not a universal source refinement |
| Rust `c1_gao.rs` Euclidean loop equals the Lean model | Still separate, notwithstanding prior invariant/differential tests |
| Root-bound raw query-log access and its resource limits | Existing instrumented graph model; real adversary/replay coupling still required |
| Acceptance forces this close code tuple and selected payment residuals | Still the global soundness obligation |

The theorem is a mathematical decoder composition, not an extracted Lean
implementation. It does not certify the fixed SHA test coins in
`recover_near` as ideal private randomness, nor replace the actual caller's
subfield/image/global-radius checks with unchecked assumptions.

For a fixed totalized C1 within 16,535 common fibres of the tuple, the existing
exact hypergeometric ledger bounds 129 or more bad fibres in an independent
uniform 513-subset by approximately `2^-137.7548`. Together with its bounded
private-sampler exhaustion estimate it is below `2^-137`. This continuation
reuses that arithmetic, and now proves the missing common-sample-to-decoder
implication. The actual sampling law, source matrix and algorithm refinement
remain requirements before applying it to the executable extractor.

It is not a bound on all accepted proof failures. Radius failure, a provider
`none`, and witness-validation failure remain distinct events. In particular,
an out-of-radius execution that returns a checked witness contributes zero
to `Pr[A and not X]`.

## Focused proof evidence

The runner pins the original Gao/circle source and cached olean hashes, Lean
4.32.0 and Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`. It imports no
concurrently changing Aspis modules. Only a missing `GaoC1Recovery.olean`
was exported once, then the new leaf was compiled.

| Target | Exit | Wall | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| Missing coefficient-leaf cache export | 0 | 3.96 s | 2,873,081,856 B | 0 |
| New leaf, first preflight | 1 | 1.60 s | 2,820,784,128 B | 0 |
| New leaf, final | 0 | 1.65 s | 2,869,493,760 B | 0 |

The first preflight over-simplified the `finProdFinEquiv` inverse identity.
It was replaced by the named `apply_symm_apply` theorem, with no budget
increase. Only the final six axiom reports are success evidence; all contain
standard `propext`, `Classical.choice`, `Quot.sound` only, with no `sorryAx`.
The final source SHA is
`f1ce93d486eb29615ce9655c3a6babc714e26429b1b5517c0cee79f4ee5a1c84`;
olean SHA is
`71f946ce7f4a25935a2709667622c1662d646e74b6af706cef056c5d16ae7043`.

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_common_fibre_gao.sh /absolute/NEW.log
python3 docs/research/v8-no-work-100-20260907/experiments/audit_soundness_resume.py --check-recorded
```

No unchanged full proof suite, SBF build, proving benchmark or private-query
log export ran. Body remains 40,282 bytes; all additional work here belongs
to formal reasoning or the specified extractor, not the verifier.
