# Serial next queue (working, not validation evidence)

Current native gate kani-resume5-compress16-raw-900 is the only live capped
scope. Never launch a second scope alongside it. Its own sampled solver file
is /tmp/external-sat3311970.Uw1pUG.cnf; preserve receipt and clean only after
termination. Final aggregate peak remains unobserved; sampled cgroup counters
are retained separately from wrapper GNU time.

After the gate ends:
- inspect verdict/counterexample, collect final metrics, confirm own scope gone;
- compile new Op223CanonicalCallsite with next unused Env-J ID41231;
- focused extraction config trial mir4: same cfg-only one-call wrapper, encode
  dependency MIR and explicit MIR opt-level4/inlining flags, root-only include;
  inspect actual emitted body and external template, never treat zero exit as
  source acceptance when compressor remains opaque;
- resume actual private tuple_cells / bank_for_row extraction to address the
  remaining registry offset input invariant (one reservation refusal retained);
- full canonical length16 output-lane0–3 Kani splits, unwind18, timeout180;
- op117 fixed-index output-lane splits with arbitrary canonical coefficient
  arrays, unwind30, timeout180;
- ruling(i) circle/unwind40 and pole1024/unwind1026 retries, timeout900 each.

Planned total Kani:2 old compressor900 retries +4 compressor lane partitions
+4 op117 partitions +circle/pole900=12. No third identical old harness run.
No new gate has been executed merely because it appears in this queue.

Lean budget30/100, next41231; final3 reserved. Continue meaningful focused
proofs toward actual producer/caller/source association until the full budget
is exhausted, or a checked canonical shipped-row counterexample is found.
