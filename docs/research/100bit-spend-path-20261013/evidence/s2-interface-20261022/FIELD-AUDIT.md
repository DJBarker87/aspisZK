# S2CallerFacts semantic field audit

This is a conditional interface, not premise discharge. `Inputs` is data
selected by a future concrete caller proof; that proof must identify it with
actual execution. No generic record inhabitation is claimed.

| Fields | Meaning | Why not a cone conclusion |
|---|---|---|
| proofBytes/publicBytes | Input snapshots equal stored/model public bytes at every reached site | No returned verifier value, decision or oracle history |
| proofSuffix/proofLength | Account proof suffix after 688-byte afterstate; exact 57607-byte proof | Input layout only |
| checkpointBytes/checkpointLength | Retained verifier-checkpoint input snapshot and width | No canonical encoding, checksum validity or returned accumulator equality |
| nodeViews | Six exact physical input slices, b<2 and k<3 | No batch verdict, scratch output, parent/leaf hash or observation equality |
| y1Input | Exact scanner input slice | Scanner success is derived separately from parser provenance |
| observerNone | Actual Option carrier is none | No observer-output or backend-trace equality; actual carrier instantiation remains required |
| reachedPrefix/callOrder | Earlier caller position reached; strict clock ordering | No oracle-history equality or preselected successful execution |
| accountFrame/writtenMetadata | Full unaffected accounts and checkpoint metadata remain unchanged | Required local account effects, not verifier-output equivalence; the permitted data write is fixed to TX1 account2, not caller-selected |
| oracle | Total per-call digest interpretation | Required local ROM/backend law; no trace-level equality or cryptographic assumption is manufactured |

`checkpoint_oracle` derives the weaker checkpoint implication from the total
multiproof law through the concrete digest/state roundtrip. `compose` returns
checkpoint caller bindings, six slot premises, S7's *constructed initial*
Progress and S8's actual reached CallerInvariant. The latter follows from an
explicit S7 PushTrace, outside S2CallerFacts. Neither the PushTrace nor raw
field meaning is inferred from readonly bytes. Saved-ten-state provenance
remains outside the record and is needed by decision_success_join.

The structure contains no eval/run/observe/Log, no accepted output or Boolean,
no arithmetic state equality, and no free per-cone Prop field. Account frame
and local digest equations are precisely the requested local effects/backend
facts; they are not the target observation/log/verifier-output equality.
The audit script checks the exact field list and rejects conclusion vocabulary.

The schedule is a coarse partial order of caller blocks. It is not a theorem
about all 140 S10 relations, each of the 22 query iterations, or whole Rust
execution. Those source lowering/ordering certificates remain independent.
