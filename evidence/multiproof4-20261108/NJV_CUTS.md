# NJV reviewed cut transcriptions

Target not yet established. Native-contract semantic transport is P6/D188 option-A RECLASSIFICATION. Every relation below is a source-ordered G built from the parent stage cuts, then instantiated with CLOSED children at SAME arguments under (y)(3)/(aq)(5). It is not an inverse association of independent logs. No XRn kit, arbitrary Ops, endpoint equality, success premise, exporter, fresh trust row or invented invocation ID.

## Frozen source and observations

Frozen revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, verify_in_place body cc8c08dc90a3b055e66141f3e0d9b67ba3df8fd7ea2f55e031e4bbe13d718c63. NJV_frozen_multiproof.rs.txt and NJV_frozen_candidate.rs.txt are retained once. NJV_SOURCE_ASSOCIATION.json pins their source and native skeleton checks; NJV_NATIVE_REUSE.json pins every reused native receipt/config. The CLOSED helper declarations are from ledger15's coherent NJE forest, not unreviewed horizontal WIP.

| Native cut | Asserted facts transcribed | Lean use |
|---|---|---|
| NJP_K013..016 | arbitrary 32-byte borrowed sibling window, exact pointer/length/each byte, missing window | NJP_NativeRowCut.siblingValues; NJV_Pending.Cut.arguments; child at SAME slice |
| NJP_K017..022 / K025..056 | per-branch arbitrary-prestate scalar, input, output and every arbitrary frame coordinate; full 9216-byte input; staged output and real write-window cuts | NJP_NativeRowCut.Cut fields: calls, kind, inputIndex/inputValues/siblingValues/orientation, writeCount/writeIndex/writeReply, countFrame/cursorValue/indexValues/digestValues/nextIndex/nextWrite/returnValue |
| NJP_K060/061 | insufficient-sibling rejection, no parent call/write, unchanged i/w/cursor/all array coordinates | native Rows.stop; no later query |
| NJP_K062/063 | exhausted row, no parent call/write, unchanged arrays/cursor; exact i/w | native Rows.halt, sets local n=w at level completion |
| NJP_K064/065 | exact 18-height controller, (i,w)=(0,0), next count threaded in order, prefix stop | NJV_NativeLevels.Invocation and induction; control ONLY, no value credit |
| NJP_K066/067 | n=0/n>16 short-circuit, SAME &idx[..n], length modulo32, child count | NJV_Entry.Guard and native Entry.rejected/returned, CLOSED well_formed reply installed |
| NJP_K068/069 | n=1/index0=0/root comparison/cursor=length terminal, short-circuit and same arguments | native finish constructor; NJP_CohortTerminal.same; CLOSED NJE_RootPackets |
| NJP_K070/071 | pending sibling frame: cursor advanced32, both buffers unchanged, exact borrowed region/orientation | NJV_Pending.Cut and abort induction |
| NJP_K072/073 | raw u32 parent/2, parity, adjacent XOR association | existing scalar/cohort transport; no field arithmetic |
| NJV_K002/003 | pending occupied frame, exact two stored 32-byte operands; no reply/write/cursor advance; corrupt idx control FAIL | NJV_Pending.Cut; previous own K001 overflow in assume excluded and fixed before bounding i+1 |

K023 TIMEOUT remains excluded; it was never rerun. The existing split full-range windows replace it. Native copies use exactly KMX bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 with matched failing controls. No multiplication, SHA body or writable static. Full raw arrays contain all 16 indices and all 16x32 digest bytes, including inactive cells.

## Composition and domains

NJV_NativeRows.Invocation fixes the actual row program counters and poststate per cut. NJV_NativeRows.observation proves native G equals the raw one-step/while program; NJV_NativeLevels does the 18-height induction. NJV_RowDomains.next_domain/all and NJV_LevelDomains.progress/all derive EVERY next cut's n/i/w/cursor/window bound from the original entry. NJV_Admission.all exports that derivation as a conclusion, not a root premise. NJV_WordDomains shows faithful raw u32 representations; NJV_ChildArguments applies the CLOSED parent laws at those SAME operands. NJV_EntryABI.initial supplies local cursor zero from the ABI rather than asking a caller for it.

NJV_Entry.observation and adopted transport full Result, both mutable buffers, cursor and ordered query/reply history to MultiproofConeVerifyState.verifyState. Early rejection retains the original arrays and emits no query. Terminal failure and missing siblings retain partial writes and all prior queries. No accepting-run premise occurs.

NJV_Pending.Cut has only active/available/arguments/indices/values/count/cursor facts at the child boundary; no returned Result and no last reply. NJV_AbortRows/Levels/Entry compose these through the SAME entry, with exact pending request and frame. NJV_AbortDomains proves the domain of its last reached cut. Under (an), runtime abortion means no later event; no Rust Err is invented. H is only used for the total-denotation comparison; abort prefixes contain only prior replies.

## Own and caller domains

The original ten-leaf unit Domain (Arity Two, positive d<=10, sorted distinct keys<2^18, exact nodeCount prefix, zero slot padding) is explicitly preserved in NJV_UnitDomain. The complete entry theorem is stronger: it handles any count/order (with rejection) in the fixed ABI under input length<=9216. NJV_CallerBounds.from_count proves that length bound on the SAME counted well-formed keys for both d<=10 and d<=12. No implication 12<=10 is claimed.

Only deployed literal Arity::Two is covered. The Eight branch/parent_with_digest is not reached at candidate::batch_tree's literal call; no Eight credit or SHA unwinding. Actual inventory callers are TX1:083 and TX2:055 batch_tree (frozen candidate.rs:202), independently retained in NJV_CALLER_CLAUSES.json with every original clause. The convenience multiproof::verify wrapper is not an inventoried deployed incoming edge and earns no credit.

Source-comment receipt-number corrections are rebuilt in L038/L040/L042; no theorem statement or proof changed.

## Final provenance freeze

After gate1, the four newly authored native-cut/induction docstrings were completed with direct harness paths, SHA256 and exact assertion excerpts required by (ai)(5). This changes source/compiled documentation metadata, no definition, hypothesis or proof. Focused replays and a second/final combined gate validate the final byte-pinned cohort. No third full audit is permitted.
