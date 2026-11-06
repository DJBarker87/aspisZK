from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
inv=json.loads((E/'NJD_INVOCATION.json').read_text()); ats=list(map(json.loads,(E/'NJD_ATTEMPTS.jsonl').read_text().splitlines()))
limits=dict(kani=100,lean=90,extraction=0)
notes={
'TX1:330':'process (TX1:333) has no CLOSED complete Result/post-state packet. The model trace is proved, but cannot discharge that child clause. Exact first/copy P7 specialization is not an admitted native law merely because Hiq defines a pure stand-in.',
'TX1:333':'stage1/stage2 are OPEN; head/copied and equality call instances must be matched to actual library ports. No full parent native cut with all child effects can be constrained to an absent child packet.',
'TX1:344':'stage1_owned (TX1:345) is OPEN. SDK acquisition/deref/drop and exclusive-copy ABI law is not supplied by the seven RuntimeEntrypointAdmission fields. NIV SDK history is an abstract model history; a foreign guard requires a pinned matching P7 or NCO law, not integer-pointer havoc.',
'TX1:345':'first_decoded (TX1:328) is OPEN. Metadata guard cuts have run; their native construction defers byte errors, so it is not a full producer/post-state packet on all snapshot values. NIS/NIV model laws do not themselves fill that native gap.',
'TX1:328':'verifier::tx1 (TX1:094) is OPEN on NIU. Constant observer and error mapping have model ports, but there is no complete CLOSED tx1 Result/heap/effects packet to substitute; candidate model equations are not native tx1 closure.',
'TX2:213':'process (TX2:221) is OPEN, for the same actual dependency as TX1:330. An independent invocation token/exporter is neither present nor required; no token is introduced.',
'TX2:221':'stage2 (TX2:240) is OPEN; the same canonical first/copy/equality primitive binding gaps apply. Lifecycle branches are excluded only under the CLOSED admitted-route law, not by deleting their source.',
'TX2:240':'stage2_owned (TX2:241) is OPEN. Snapshot SDK ABI and Clock::get full error/cleanup carrier law remain uninstantiated. RuntimeClockSlotBinding constrains the successful slot only; it cannot be expanded into a success/ABI/error law.',
'TX2:241':'validate_asq8 (TX2:242) and observer (TX2:212) remain OPEN. Every stage also needs the complete encoded Vec/callee Result and heap/cleanup cuts. No whole-vector probe is substituted for those cuts.',
'TX2:216':'decode_pool_v1_pair_forest_checkpoint_v1 (TX2:152) is OPEN and outside this job function list. Box construction/ownership requires a complete decoder reply. Record the slice boundary; do not invent a successful box.',
'TX2:217':'The independent digest iteration K018/K019 and mapped digest law are complete local results. Remaining: actual iter_mut selected-node/frontier association, all header/range producers, zero-tail loop, Box ownership/cleanup and adopted op50 whole-lane endpoint. No emitted full lane body is supplied by NIV_L022 (op50 is opaque); zero extraction budget forbids obtaining a new one here. A reviewed whole-body substitution would need separate authority, not a new hypothesis.',
'TX2:218':'decode_pool_v1_pair_forest_master_v1 (TX2:153) is OPEN and outside this job function list. Full decoder value/error ownership and allocator frame cannot be supplied by the small outer Box wrapper alone.',
'TX2:233':'decode_master_box/checkpoint_box/lane (TX2:218/216/217) and registry authentication (TX2:234) are OPEN. Independent readonly/checkpoint guards were attempted. Exact SDK Pubkey::create_program_address law/seed/frame and complete decoded-record associations remain missing; entry admission does not supply them.',
'TX2:234':'V1 registry and entry decoders TX2:203/201 are OPEN outside this job list. V2 CLOSED rows are identified in NJD_INVOCATION, but their uses still need full producer/canonical record cuts and exact create_program_address seed/reply/frame law. There is no admitted PDA-value law in RuntimeEntrypointAdmission; NCO would require a new reference extraction, budget zero. No digest/curve implementation is unwound.',
'TX2:242':'authenticate_asq8_accounts TX2:233 is OPEN. CLOSED request/output-lane/scan/reconstruction rows are listed for the exact decoded arguments; no successful authentication clause can be retained as a root premise.',
'TX1:329':'The deployed body returns literal None. Direct Option<fn> value/None assertions remain quarantined. (ae) permits Result/state/effect assertions for functions called with a constant None parameter; observer() itself has no such parameter and returns the quarantined carrier. No assertion independent of that carrier establishes its value. No rename is attempted to obtain a verdict.',
'TX2:212':'Same observer-carrier obstruction as TX1:329, on the same frozen body. Model None is known; native Result/effect comparison on a legal deployed instantiation is not an Option<fn> value proof.'}
text=['# NJD remaining obligations','','Target not yet established. All 17 assigned occurrences remain OPEN on NIU ledger13. No status promotion is proposed.','', '## Budget and stop discipline','', 'Kani and Lean limits are ceilings, not evidence. Remaining budget is not permission to rerun probes or a timed-out shape. Each full member is blocked on its actual child/library/carrier law below; independent licensed cuts were attempted rather than held behind unrelated children. The remaining SDK/PDA laws require matching pinned P7 facts or NCO reference extraction; this job has zero extraction budget. The inventory records candidate P7 names separately from admitted laws. No new trust or extraction has been introduced.','', 'This is below 80% of the allocation. Each remaining complete member lacks the exact prerequisite law or permitted carrier realization listed below. Kani cannot assume those laws; a fresh NCO extraction is outside the zero extraction budget, outside-job OPEN callees cannot be declared CLOSED, and direct observer value assertions remain quarantined. Independent guard and lane-step cuts with available laws were attempted, and their remaining model laws were completed. Additional partial fragments remain conceivable, but none is an admitted replacement for the named missing clause. This is an incomplete entry-layer result, not a target closure or an assertion that every possible supporting lemma is impossible. The member-by-member stopping inventory follows.','']
for r in inv['rows']:text += ['## '+r['row']+' '+r['function'].split('::')[-1],'',notes[r['row']],'']
text+=['No Lean-only theorem can manufacture a missing native ABI/callee realization. The new model trace/frame and digest laws are audited separately; no root takes an undisclosed child equality, parent success, independently selected post-state, or address-implies-payload premise.']
(E/'NJD_REMAINING.md').write_text('\n'.join(text)+'\n')
(E/'NJD_CLOSED.json').write_text(json.dumps(dict(schema_version=1,status='NO_NEW_COMPOSED_ROWS',functions=[],rows=[],new_composed_functions=0,new_composed_rows=0,gate='NJD_AUDIT.json',credit_waits_for_next_ledger=True),indent=1)+'\n')
bp=E.parent/'ledger13-20261107/NIU_LEDGER.json.xz';raw=lzma.decompress(bp.read_bytes())
(E/'NJD_LEDGER_DELTA.json').write_text(json.dumps(dict(schema_version=1,baseline=str(bp.relative_to(E.parent.parent)),baseline_archive_sha256=sha(bp.read_bytes()),baseline_raw_sha256=sha(raw),frozen_revision=inv['frozen_revision'],changes=[],new_composed_rows=0,reason='No complete parent invocation packet; all NIU statuses preserved'),indent=1)+'\n')
(E/'NJD_CUTS.md').write_text('''# NJD stage cuts

No complete entry row is claimed. NJD_guards.patch supplies eight named callee-boundary cuts, one per actual stage1_owned/authentication guard use: arbitrary flags, keys/owner, length Result and log seeds, constrained explicit-constructor helper reply, same argument handles, complete ProgramResult, exact local log updates and metadata coordinate frame. K002-K017 are the eight positive/control pairs; K001 records the invalid original snapshot constructor. Each control fails the intended assertion, not a timeout or compilation error.

The native constructor uses deferred bytes Err, with paired AccountBorrowFailed when length borrows fail. This is a strict limitation: valid successful byte Vec payloads/ownership/cleanup are not represented. It cannot silently become an all-account domain. NJD_GuardCuts.cut transcribes only the asserted metadata coordinate and Result/log facts. CLOSED helper model laws independently establish unread-byte irrelevance; they do not create a native full-state certificate. The keyByte/handle interpretation is an uninstantiated P6/D188 transcription port, not address-implies-payload.

NJD_lane.patch K018/K019 checks ONE actual decode-call/assignment/empty-subtree continuation on arbitrary pre-node, level<20, next<=capacity and all32 raw bytes. The explicit decoder computes all eight natural u32 words, rejects noncanonical words, logs argument pointer/len/selected word and returns the exact mapped Result. A successful decode assigns the node BEFORE the later empty-root guard, including its Err branch. NJD_LaneStep.cut transcribes the selected coordinate, pointer, length, call count and logged index/word only. It does not assert the missing parent iter_mut/frontier association. NJD_DigestLaw.stub_source pairs this stub with the CLOSED NFY decoder on every input, including errors. The pure write/frame/disjoint-chain laws are not a native iterator certificate.

NJD_Trace and NJD_EntrySpine give chronological model call composition and erasure to NIV’s emitted entry/process. Admission/head/copy/comparison/selected-child calls retain exact arguments and complete results. Fail/div retain the entered call and have no suffix. NJD_Prefixes supplies the exact two TX1 model traces. None supplies the missing native parent-to-trace relation or CLOSED child clauses.

KMX_slice/ptr controls K021-K024 recheck canonical copy stubs under the same deployed offline configuration. K020 was a wrong CLI-qualified path (nested KMX_checks omitted), not a proof verdict or a rename-stability experiment. No multiplication, SHA unwind, writable static, new function contract or new trust row is used by these cuts.
''')
patches={n:sha((E/n).read_bytes()) for n in ['NJD_guards.patch','NJD_lane.patch']}
kmx=subprocess if False else None
(E/'NJD_CERTIFICATES.md').write_text('''# NJD reviewed transcriptions

All entries remain OPEN as parent certificates. Native-contract semantic transport remains owner option A/P6/D188 reclassification; no trust is added or removed.

| Cut | Native assertion transcription | Domain / missing composition |
|---|---|---|
| NJD_GuardCuts.cut | `out==reply`, same logged account/owner pointers, writable/kind, `calls==1`, failed tag, arbitrary key/owner byte plus flags/length frame | Metadata/deferred-error native class only. Full byte Vec, allocator and caller-frame association not discharged. |
| NJD_LaneStep.cut | result success bit and exact error variant, `node[index]` equals decoded word or old word, exact input pointer/32-byte length, calls/index/word | One arbitrary loop step. Full input/frame iteration and op50 whole-body/model association OPEN. |

Exact patch SHA256:
'''+''.join('- '+n+': `'+h+'`\n' for n,h in patches.items())+'''
Transcriptions contain no successful endpoint or whole-child equality. Guard and node observations remain coordinate observations; universal/frame lifting is a separate obligation. Root statement inspection is in NJD_L022 stdout and NJD_ROOT_INVENTORY.json. No native positive root satisfying (aq)(2) has been authored/admitted: free generic ops in the model theorem are not CLOSED child packets. Conditional support lemmas are not candidate root theorems.

Every scope receipt supplies target, command, source revision/hash, dependency/library pins, exit, wall, RSS and swap. Each new top theorem prints axioms; failed diagnostics are retained but excluded. Native receipts carry frozen graph/lock checks, features, optimized/offline environment and own NJD_target. No inherited probe earns new native credit.
''')
(E/'NJD_STUBS.md').write_text('''# NJD stub / law / domain table

No field multiplication stub is used; LPh_STUBS.md is unchanged.

| Native stub | Paired law | Domain / interpretation |
|---|---|---|
| NJD_stages::logged_guard kind0 | NJD_GuardCuts.readonly_source / readonly_step; CLOSED NFU_AdapterGetters.readonly | All metadata flags; native bytes deferred Err only. No promotion to arbitrary native Vec/cleanup. |
| logged_guard kind1 | CLOSED NHJ_ReadonlyPacket.readonly (canonical forest) | Same owner and metadata; requires full packet installation and key interpretation. Native metadata class only. |
| logged_guard kind2 | CLOSED NHJ_CheckpointPacket.substitute and NGL_CheckpointModel.result | Exact same snapshot-domain length Result, expected1768, writable flag and owner. Full native snapshot/byte-frame extension remains OPEN. |
| NJD_lane::decode | NJD_DigestLaw.stub_source; NFY_NBP_DigestDecode.result / NFY_NEQ_DecodeScalar.digest_result_state_effects | Every32-byte input, all eight canonical/noncanonical word cases, mapped Err InvalidAccountData, no multiplication. Native input-coordinate/record to Aeneas Array association remains a reviewed transcription, not a new axiom. |

All logs are local mutable records passed by &mut. Explicit Result constructors cover each helper’s reachable error domain; no typed guard is fabricated from raw bytes. No stub_verified/proof_for_contract or pointer-valued oracle is introduced. No RuntimeCpiReadonlyEntry7, XRn join or new trust row.
''')
print(json.dumps(dict(rows=len(notes),new_rows=0,kani=sum(r['attempt'].startswith('NJD_K') for r in ats),formal=sum(r['attempt'].startswith('NJD_L') for r in ats))))
