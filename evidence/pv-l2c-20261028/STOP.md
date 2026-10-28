# D370 current disposition — checked N3 counterexample

Target not yet established. Successful canonical preparation can retain raw
M31(P) at C1[0][444]; native masking preserves it and N3 rejects it, whereas
the same-public M31(0) case passes the exact-body guard diagnostic. The actual
secure prover entry with OS entropy returns Err(Semantic) on the bad case.
Work stopped under the explicit counterexample rule, with 97 Lean attempts
unspent and no new Kani. V352/V354/V357/V360 remain OPEN/P; zero premises
removed, added, weakened or changed. Frozen implementation and HonestInput
are unchanged. Current evidence and accounting:
[resumed finding](resume-d369/D370-FINDING.md),
[state reconciliation](resume-d369/RECOVERY-D370.json),
[native receipt](resume-d369/canonical-n3-probe5/receipt.json).

The earlier dispositions below are historical and superseded by this finding.

---

# Current disposition after D355/D356 recovery

Target not yet established. Resume allocation exhausted: 72/72 Lean attempts
(55 pass, 17 fail), zero new Kani. Including prior work: 140 Lean, six Kani.
Final corrected-closure audits 44897/44898/44899 all passed with standard
axioms. Both exact-carrier fixtures are audited. V352/V354/V357/V360 remain
OPEN/P; no endpoint premise removed or weakened. Recovery launched no runs.

The current detailed report, complete attempt inventory, recovery receipts,
remaining obligations and stop reason are in
[RECOVERY-D356.md](resume-d355/RECOVERY-D356.md),
[RECOVERY-D356.json](resume-d355/RECOVERY-D356.json) and
[RESULTS.json](resume-d355/RESULTS.json).

The earlier allocation's report below is retained as historical evidence;
its missing audit/ID-allocation status is superseded by the current receipts.

---

# D355 stop: 72 continuation Lean attempts exhausted

All 72 authorized Lean compiles were actually launched and have recovered
receipts: 55 passed, 17 failed. IDs 44800–44868 and 44897–44899 were consumed;
44869–44896 remain unused. Prior work launched 68, for a total of 140. Zero
new Kani runs; the prior six remain historical, with no usable copy-dependent
PASS credited. Refusal at 44800 consumed neither its ID nor a compile; the
same ID was retried after cooldown, in accordance with (m').

Final combined/fixture/focused audits 44897/44898/44899 all passed. The final
1456-object public/private import closure fingerprint check passed, with
unchanged toolchain and only permitted standard axioms. This supersedes the
historical failed audit described in PUBLIC-IMPORT-FINDING.md.

Target not established. V352/V354/V357/V360 remain OPEN/P bucket b. Zero
premises removed, added or weakened. No checked honest-input guard
counterexample was found. CanonicalityBoundary is a diagnostic on arbitrary
raw words, not such a counterexample. No new bad event or trust field.

Next deliverable: universal native sampler/producer and consumer association
on precisely ConsumerBoundary25.HonestInput, raw compiler bank canonicality,
helper materialization/inverse boundary and native sumcheck provenance.
E1/E2 complete streams and failed-prefix observation coupling remain P.

No frozen implementation change, deployment, push or wallet/key operation.
Raw receipts, failed inputs and current-source accepted index are retained
under resume-d355/. The pinned private cache remains for dependent reuse.
