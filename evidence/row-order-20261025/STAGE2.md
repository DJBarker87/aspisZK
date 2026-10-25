# SAME traced pair with history

`lean/RowOrder_AcceptedPairHistory.lean`, theorem
`AspisR1.RowOrder_AcceptedPairHistory.accepted_pair_history`, starts from
SInt2's accepted_pair_claims. It destructures that one witness and retains
f/s, SourceCuts, outer expanded/owned executions, schedule, account observations,
post2 frame, selected semantic Claims and Required14. The new history consumer
is applied to THOSE cuts and THOSE actual accepted wrapper outputs.

The output additionally constructs the concrete CheckpointVersionBinding on
the SAME saved Vec and s.checkpoint and proves its key, ledger and events equal
the runtime premise's fields. It derives checkpoint/proof/public byte identities
and checkpoint length1768. There is no SourceCuts/caller-output/second-execution
hypothesis. CheckpointVersionBinding on actual post1 and P2Prime remain named
runtime premises. Writer/reader and first-entry/multiproof/S8 ports remain named
child premises, as in the inherited theorem. Trust, candidate adoption, carrier,
failure event and security metric do not change.

Attempt006 checked the weaker existential history output. Attempt007 strengthened
the result to preserve key/ledger/events explicitly; no unchanged compile rerun.
007: exit0,2.113133862s,peak5248620KiB,swap0,source5650ee5670 dirty with exact
SHA in receipt, only [propext,Classical.choice,Quot.sound]. Both used the pinned
coherent host workspace and -M7000 under6G/8G/swap0/tasks64. Full statements,
commands, dependency hashes and axiom audits are in the receipts. No source/body
runtime refinement or history protection is newly discharged.

Budget7/100 Lean,0/60 Kani. This closes the concrete history-instance assembly
on the existing D189/Claims witness, conditional on the stated runtime/child
premises. It does not construct a raw canonical frozen2 join.
