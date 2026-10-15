Extracted public serializer to fixed raw carrier: Lean 4.31

final-green contains the exact pure Core and full bridge sources, successful
receipts/logs, and optional compiled objects. Sequential focused results:
  core-a: exit0, 6.204s, sampled group RSS1264064KiB, process swaps0;
  bridge-b: exit0, 21.747s, sampled group RSS3113872KiB, process swaps0.
The full bridge's ten #print axioms outputs contain only propext,
Classical.choice and Quot.sound. Core defines the pure carrier and serializer;
it has no named theorem audit. No sorry/custom axiom is present in final sources.

precursor-green retains the exact byte-only bridge and its successful check:
bytes-a, 17.984s, sampled group RSS3039216KiB, process swaps0. This was checked
before composing the full projection. failed-attempts retains bridge-a's exact
source, receipt and diagnostics. Its sole failure was the twenty fixed Fin
indices left after list enumeration. A bounded rfl closes that equality in
bridge-b; it does not reduce field values or a large arithmetic recurrence.
The failed run's error-recovery sorryAx is not a successful proof audit.

source_success_raw starts with successful return of the actual extracted
public_bytes. It proves PublicRawCore.serialize (project p) equals some of
the output bytes converted by bv.toFin. project is a fixed fieldwise map,
including the live snapshot index/frontier and candidate root/frontier.
Canonicality is derived from success. No capacity, positivity or assumed
serializer-refinement premise occurs. project_words and project_bytes prove
the literal variant ordering, option tags, and complete arrays symbolically;
wordBytes_agree and indexBytes_agree cover the bounded LE4/LE8 conversions.

pins.json records exact prerequisite source/object hashes, observed backend
references, compiler version and shared libraries. The launcher hash alone
does not distinguish installed Lean versions. Referenced prior bundles retain
generated Types/Funs, extraction pins and earlier helper proofs. Dependencies
were reused, not rebuilt. Final source hashes match successful receipts.

The runner retains local absolute cache paths, Lean -M6000 and a sampled 7GiB
process-group stop. This is not a cgroup cap; process swaps0 is not a claim
about system swap. No package-wide replay, cold build or host Lean was run.

The identical Core source also has a separate Lean 4.32 check. The sibling
lean-public-raw-core-agreement-432-20261015 bundle proves agreement with the
existing PublicSourceRaw serializer, including its noncanonical rejection.
These are two kernel checks; no cross-version object was imported, and no
single-kernel end-to-end theorem is claimed. Rust extraction/compiler and
runtime/allocation correspondence remain trust boundaries. Zero withdrawal
remains serializable; payment amount guards are separate. Full J1.a closure
is not claimed.
