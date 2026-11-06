# TX2:065 source-ordered invocation inventory

TX2:065 OPEN; target not yet established. Baseline is NIU ledger13, not historical local callee status. Source inputs are pinned once in NJC_INPUTS.json.xz; parent is NHT_EmittedCommon.tx2_common. Entries below are source occurrences, never independent invocations. An entered `?` retains Err, outer fail/div and its executed prefix; no suffix is fabricated.

| Order/site | Decoded SAME arguments | Ledger / complete law or exact gap |
|---|---|---|
| 1: op18 | D, checkpoint, proof, public_bytes, S2, hash | TX2:124 OPEN: NJC-M01: actual frozen resume full Result, returned Box/payload/ownership and prefix frame; NIY_ResumePort.source is reference transport only. |
| 2: op17 | 29, SAME p.gamma | TX2:138 CLOSED: NFW_PowersCohort.source; caller derives canonE on SAME resumed gamma, then nominal-array map. |
| 3: op13.1 | none, CheckpointRead | TX2:118 CLOSED: release None only; NFS_QueryLoopRoot.root is a loop theorem, not the mark body; use exact emitted mark/None reduction, no K-2-dependent Kani credit. |
| 4: op2 | proof[7495..7527] | TX2:031 CLOSED: NET_WideModel.result / NHV_InactivePacket.source; complete Option + outer fail/div. Range domain from SAME proof length. |
| 5: op5 | D, SAME proof, SAME p, proof[7751..7783] array32, 1, hash | TX2:053 OPEN: NJC-M02: complete Merkle5 Result/effects, idx/val frame and abort-prefix; sibling NJA only after merge. |
| 6: op13.2 | none, Merkle(10) | TX2:118 CLOSED: same None law as op13.1; entered only after op5 Ok. |
| 7: op11 | SAME p.queries, SAME a.next (=10), 22 | TX2:104 CLOSED: NFN_NFB_GeometryComposed.result_state_effects; NHV_NativeOps.geometry_result forgets only a proven pure frame. |
| 8: op10 | SAME a.weights.deref | TX2:100 OPEN: NJC-M03: actual native constructor occurrence and complete allocation/copy/frame association; NHV_PendingPacket.source is emitted/model packet, width64 must be derived. |
| 9: op6 | SAME proof,p,a,g,none,geometry,pending,22 | TX2:058 CLOSED: NFS_QueryLoopRoot.root + NHT_PacketOps.query_source; NJC-M04: SAME native query6 producer and full payload carrier (no address-implies-byte rule). |
| 10: op9 | SAME returned pending, SAME returned a1.weights mutable slice | TX2:099 OPEN: NJC-M05: full native flush Result + complete mutable frame, then actual deref_mut_back reconstruction. |
| 11: op19 | S2 View, SAME p, post-flush accumulator, none | TX2:115 OPEN: NJC-M06: SAME-call NIG_FinishInput.Domain; actual new/pair/finish complete installation; seven/seven/64 canonical windows from actual history. |

The emitted standard calls between these sites are also retained in order: resume Try.branch; `a.next != 10`; constants/range7495..7527; Option.ok_or(Parse)/Try.branch; range7751..7783; TryFromArrayCopySlice32/unwrap; Merkle Try.branch; geometry Try.branch; Vec.deref; pending Try.branch; query Try.branch; Vec.deref_mut; flush; deref_mut_back; empty semantic/y1 arrays; ranges7527..7751,7783..8007,8007..10055; empty query array; finish. Each range keeps outer bounds failure; unwrap keeps its nonreturn branch. None is silently assumed successful.

## Resume nested occurrences

The first parent call enters the frozen resume body. Ordered guards precede every tail read: checkpoint_size(S2)=1768; magic bytes0..8; tag(S2) at8; next9<=22; flag10=1; zero bytes11..16 (`any` callback); end=len-32; digest([proof]), digest([public_bytes]), digest([checkpoint domain tag, bytes[..end]]), each at its literal short-circuit position. Digest values use the approved runtime realization; arguments/replies/prefix still need native association. Public is exactly the parent public_bytes: no 688/1880 length is inferred from pointer identity.

Tail after successful header: raw32 state@80; raw32 root0@112; raw32 root1@144; E gamma@176; E kappa@208; E alpha0@240; E alpha1@272; K rho@304; raw4/u32_le query[i]@320+4*i for i=0..21, in order; validate_checkpoint_queries(SAME array22); semantic_alpha(SAME bytes,408), ten K reads; K z0.x@568; K z0.y@584; K z1.x@600; K z1.y@616; E claim@632; E rhs@664; K power@696; final_len(S2)=64; filled64(K::ZERO) and Allocation mapping; read_weights(SAME bytes,712,SAME reserved vector), 64 K reads; final cursor=end=1736 guard; next9 cast; Box::new with exactly these Prepared fields, returned with SAME weights/rhs/power/next. Every intermediate error returns its actual prefix.

Nested ledger status: TX2:096 final_len CLOSED (NFQ_Transport.final_len_reference); TX2:098 tag CLOSED (NFY_NFD_RawCarriers.tag_result_state_effects); TX2:112 checkpoint_size CLOSED (NFQ_Transport.checkpoint_size_reference); TX2:045 filled CLOSED (NIG_FilledCoverage.source) but SAME native reservation/resize producer and allocator frame association remain NJC-M07. Reader E/K/raw TX2:105/106/107 OPEN; semantic TX2:121 OPEN; weights TX2:122 OPEN; validation TX2:126 OPEN. Exact missing laws NJC-M08: arbitrary entered Reader pre-state -> complete Result and returned Reader plus backing/frame at SAME raw/E/K calls; NJC-M09: semantic10/read_weights64 one-step native association plus induction and abort-prefix frame; NJC-M10: full validation Result on SAME ordered query producer. NIY reference laws do not change these ledger statuses.

canonical_scan TX1:084 is only the retained history producer child law, outside the direct parent. Its nested iteration/source association remains NJC-M11. Opening TX1:085/TX2:056 is CLOSED: reuse NFN_NEO_TailReference.checked/opening in owner module NFN_GeometryPart05 at SAME index/proof; no new getter facet.

## Gate interpretation

An (aq) clause must be proved with the listed theorem and SAME decoded arguments, including full post frame. Ledger CLOSED does not by itself prove the parent domain. No clause is accepted as a root hypothesis. Until every M01..M11 and caller domain is installed, no positive native root theorem or ledger promotion is claimed.

## Installed clauses and current split

NJC_OrderedCalls consumes the CLOSED mark/None law at both phases and the complete powers29 law at the SAME gamma. NJC_QueryOccurrence derives its canonical domain from the same successful reference resume; that reached-branch lemma is not a root premise. NJC_ClosedCalls installs literal parser/geometry children in the source-ordered parent. NJC_ValidateCalls installs the complete freshly emitted validator at the nested resume call; NJC_ResumeCalls and NJC_OrderedCalls compose through NIY_ResumePort.source. The printed parent retains an arbitrary base dictionary and unbound native resume primitives, so TX2:065 stays OPEN. NJC_REMAINING.md is the exact current M01–M13 inventory; old baseline statuses above are not silently changed.

NJC_ValidatePort.source/frame and NJC_ValidateResult.source are the candidate complete TX2:126 child law, on every array22 (no acceptance or uniqueness precondition). Admission/credit waits for the next ledger gate. NJC_RawPort and NJC_RawWindows preserve complete Result/backing through explicit unwrap/parser boundaries; they do not silently identify the concrete debug-bearing unwrap. NJC_ScanViews uses CLOSED opening bytes at the same arguments; a pointer never proves payload contents.
