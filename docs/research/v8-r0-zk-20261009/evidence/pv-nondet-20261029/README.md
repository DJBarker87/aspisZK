# Build-instance object differences (D510)

Found by pv-evhc (branch codex/pv-evhc-20261029, commit a9e257258a, cohort-overlap.json).
Two pinned Lean object cohorts on the build host give different .olean SHA-256 for 118 of
6,002 shared modules:
- event cohort: codex-pv-runjoin-20261026/runjoin32-lean (privacy candidate, b51b1040f2);
- NDR cohort: codex-cx-reconcile-cache-20261028/objects (Stream A, research 06f74c902f).

The lean-toolchain (v4.32.0, same host executable) and every lake-manifest.json are identical at
both revisions. Lead check: 93 of the conflicting project modules have byte-identical source
blobs at both revisions; Mathlib/Aeneas modules come from identical manifests; one module
(R1FirstFold) was not located by path, and pv-evhc2 verifies it. The full source-identity check
for all 118 is pv-evhc2's stage 1.

Status: the cause is NOT established. Candidates are true compiler nondeterminism, or differing
build options, paths or environment between the two build instances. Until it is explained, an
object hash match cannot be assumed across separately built cohorts. The final release replay
must either rebuild from a single cohort or demonstrate bit-reproducibility for these modules.
Resolution for the agg16 consumer compile: ruling (h6'), one authoritative cohort (NDR).

modules.tsv lists every module with both hashes and both object paths.
