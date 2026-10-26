# CPS source and interface audit

Target not yet established. L094–L096/L180 remain open. No trust adopted.

Read the S2 handoff, plan, diagnosis and interface under
`docs/research/100bit-spend-path-20261013/` (the requested short paths resolve
there), C3-BIN's 2026-10-23 01:20 addendum, both runtime handoffs, and CPR_ sources.
The approved SDK contract concerns per-entry borrows, not parent settlement.

`T2R_Top.deployed` independently quantifies e1/e2 and their accepted wrapper
equations. Its interface contains no transaction identifier, parent outcome,
bank lineage, fee payer, durable nonce, or deployed physical-key-to-cell map.
`Entry` has physical public-key metadata but its Nat cell labels are local.
`Hist_RuntimeEntry.Layout` and `CPP_BankState.Bank` introduce an operational
projection; neither is constructed by the original root. `Bank` explicitly
documents association with a deployed executor as an outstanding proof gate.

`CPP_AtomicRecordNative.result` identifies the recorder with the same supplied
CPP schedule, not with an independently available deployed executor. Its
extraction premise identifies native verifier calls, not bank actions.
`CPR_PhysicalTop.deployed` therefore correctly retains `entry1`, positive
funding, physical-key eligibility/adjacency, tentative final image, final parent
status, reader load and ordered-event interpretation. None is an approved
additional runtime trust item. Copying them into a structure would not close
the requested rows.

Next: focused CPS proofs about parent status and the precise interpretation
boundary. Do not claim a counterexample to all accepted cryptographic root
hypotheses from the existing CPR key/event algebra countermodels.

No compiler, Kani or build has run at this stage; no release result. Source
revision and inspected source SHA/size pins are in CPS_BASELINE.json. Shipped
source, features, wire format, toolchain and inherited three ELF pins unchanged.
