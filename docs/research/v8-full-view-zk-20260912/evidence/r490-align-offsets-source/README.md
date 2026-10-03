# R490 align-to-offsets translation failure

This is evidence of a failed Aeneas translation, not a Lean result or a proof.

The R490 attempt imported the pinned LLBC then terminated with exit status 2
at `Aeneas__FunsAnalysis...visit_rvalue` (`llbc/FunsAnalysis.ml:176`) on
`Invalid_argument "option is None"`. No generated Lean target was accepted,
and no formal axiom report exists. The exact source LLBC is archived here as
`R490AlignToOffsetsSourceSelection.llbc`; its SHA-256 is
`384d170f403306449c7435e81da6050ae3f447b28a9ab0dc881450c9322621af`.

R488 capture d is recorded here only as the input provenance for the source,
flags, selectors, and compiler-evaluated size/alignment globals used to make
that R490 LLBC. It was a successful Charon extraction, not an Aeneas
translation or a source-correctness proof. Its exact LLBC is archived as
`R488ActualParser.llbc`; its selection manifest is `r488-selected-offsets.json`.

The original logs are archived as `r490-aeneas.log`,
`r488-charon.stderr.log`, and `r488-charon.stdout.log`. The command check,
manifest, and literal-global diagnostic used in the R490 attempt are archived
beside them. `SHA256SUMS.txt` records original and archived byte hashes.

`literal-candidate-b/` separately preserves the later literal candidate b
translation failure, including its complete LLBC, launch record, receipt, raw
log, and per-file checksums. It is not a successful generated-Lean target.

`literal-candidate-c/` separately preserves candidate c's complete LLBC,
launch record, receipt, raw log, and pre-R484 adapter manifest/source-snapshot
hashes. It is also a failed translation, not a generated-Lean target.

`literal-candidate-d/` preserves the later successful Aeneas translation,
including all generated files and translation metadata. Its generated external
template still declares an axiom, so it is translation-only and unverified.

`literal-candidate-e/` preserves the later successful translation with the
R493-built translator binary. Its external template still contains the
unfilled `SliceU8.len` axiom; it is translation-only and no Lean proof was
compiled.

`r493-slice-len-builtin-alias/` preserves the exact small translator-source
patch and the successful capped tool-binary build. No translation or Lean
compilation was run for that build.

`r494-parser-iterator/` preserves the selected parser iterator LLBC capture,
its source pins, successful receipt, and complete records for its two failed
attempts. It is capture evidence only, not a formal proof.

`r495-parser-iterator-dependencies/` preserves the follow-on selected LLBC
capture for the transparent `split_at_unchecked` and
`unchecked_sub::precondition_check` dependencies, with a compact R494/R495
declaration comparison. It is capture evidence only, not a formal proof.

`literal-candidate-f/` preserves the later successful concrete-builtin
translation and its focused Types success and Funs failure. The Funs failure on
missing cached `Usize.div`/`Usize.rem` aliases means the helper is unproved.

`r497-slice-len-concrete/` preserves the exact concrete matcher source patch
and release tool-build evidence. `r493-matcher-runtime-diagnosis/` preserves
the pinned runtime matcher diagnosis supporting that exact source name. Neither
directory is a Lean proof or source-correctness result.
