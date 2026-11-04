# NGR hypotheses and exact boundary

Target: `AspisR1.NGR_HISTORY.saved_to_loaded`. No cryptographic hypothesis,
SameExecution record, or post-write/load byte equality is an input. The theorem
is universal in all packet digest replies: persistence needs no digest-value
assumption. Upstream must instantiate these with the SAME producer's replies.

The abbreviation below is a deterministic value, not an existential witness:

```
saved := NGC_KNE_Writer.returned prepared accumulator domain hp hu hc
```

It has definitionally the same carrier as `alloc.vec.Vec U8`. Its 1768-byte
length is proved by `checkpoint_length` from the committed KNE/LPm return laws.
`domain : NGC_KNE_Caller.WriterDomain prepared accumulator` is the CLOSED local
writer packet's exact domain; native producer establishment remains OPEN.

| Hypothesis | Source and responsibility |
|---|---|
| `game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions n1 n2 copy allocator id` | Approved game a–d, unchanged: consecutive entries, shared global CP key AND public key, no intervening touch, successful parent, physical source actions including the actual copy. `CPH_Game.next` derives adjacency; `CPH_Trace.derive` derives the two source runs. |
| `native_writer_result : S2W_D189Wrappers.first n1 copy allocator e1 id data1 state1 = ok (.Ok (saved, post1, final1))` | **OPEN native result**, exactly one returned wrapper result whose value is the deterministic KNE packet output above. TX1:186 / prepare / Prepared producer must discharge it for the SAME prepared/accumulator/domain/digest replies/input/execution. There is no separately quantified saved vector, no second accepted run, no output-equality premise outside this named observation. This theorem does not certify the producer. |
| `protection : CPH_Protection.Facts p t saved id` | CLOSED conditional source packet (`CPH_Protection.derive`, also a headline conclusion). Expanded: afterCopy owner=id; initialized CP; positive starting funding; physical events preserve the CP; final CP cell equals afterCopy cell; final lamports at least afterCopy lamports. These source facts are **not** game fields or RuntimePersistence consequences. They must be instantiated from that packet on this SAME run; NGR does not add a trust item for them. `protected_image` projects only final data and nonzero funding. |
| `ordinary : CPG_Projection.ordinary p system t ((p.layout t).handles 2).1` | Explicit domain of the approved RuntimePersistence row: CP nonsigning and non-system-owned. Not silently obtained from numeric slot 2; actual source admission must establish this exact predicate. |
| `RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw (CPG_Projection.adjacent p) (CPG_Projection.ordinary p system) (CPG_Projection.before p) (CPG_Projection.tentative p) (CPG_Projection.success p) (CPG_Projection.loaded p)` | ACCEPTED runtime trust, owner 26 Oct. DATA ONLY. `persisted_bytes` proves its successful/funded projection here. No owner, lamport, privilege or epoch preservation is derived from it. |
| `_valid1 : S2Trust.Valid e1.heap` | Exact TX1 physical reference admission, retained as the std domain. Not inferred from RuntimePersistence; source RuntimeEntrypointAdmission establishes it. It is stronger than the purely mathematical copy lemma needs and is deliberately explicit at the physical interface. |
| `std : S2W_TrustedStd.TrustedStd copy` | Accepted std primitive, on valid physical references. `native_copy_length` inverts this SAME accepted wrapper to prove its equal-length domain, rather than assuming destination size; `native_written_bytes` derives post1 account2 bytes. |
| `sdk : S2TrustedSdkBorrow L`, `related2 : L.related w2 e2.heap`, `valid2 : S2Trust.Valid e2.heap` | Accepted SDK law and exact TX2 reference/heap realization. Existing `S2W_D189Entry.native_buffer` turns the proved e2 account6 value equality into the actual SDK payload observation. No native borrow success is assumed. |
| `allocator : S2W_D189Wrappers.Allocator A` | Existing allocator interpretation; success/cleanup comes from native_writer_result, not an allocation-totality premise. |

Other binders are statement parameters, not laws: transaction/allocator/SDK
world types, bank observations, transactions, entries, physical action list,
native functions, copy/library/state values, program/system keys and digest
replies. The deployed instance fixes id=CPH_Program.verifier and the accepted
system key. The theorem remains valid for every instance of the exact domains.

Outputs: adjacency/key/parent/copy facts, length1768, loaded bytes=saved bytes,
full U8 list equality for TX2 account6, TX1 account2 post-write payload bytes,
TX2 SDK payload bytes, and CPH_Trace.Facts. All use this one saved value.
No proof/public carrier equality, Pool settlement, hash collision elimination,
or physical driver/source-to-ELF realization is claimed.

The additional `history_statement` corollary supplies exactly
NGP_L159.History_statement, by replacing the law-free Cuts.saved and
Cuts.checkpointRead fields with the deterministic returned value and account6
entry buffer. It adds no byte-equality premise. `otherCuts` carries no law and
its proof/public/Pool values are not certified by this theorem. Full loaded
binder types are printed with pp.all in NGR_L020/stdout.log.
