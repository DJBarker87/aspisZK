from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
v=json.loads((E/'NBV_VALIDATION.json').read_text());assert len(v['attempts'])==57
sha=hashlib.sha256((R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()).hexdigest()
def write_sections(name,text):
 parts=text.split('\n## ');p=E/name;p.write_text(parts[0])
 for part in parts[1:]:
  with p.open('a') as f:f.write('\n## '+part)
common='''Frozen Rust4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; headline
AspisR1.RPx_Deployed.deployed; L154 statement parameter; narrowed D188,
frozen3, RuntimePersistence and the approved game unchanged. Digest/error
cohort slots are op43/op44, correcting the old inventory's op48/op49.
No headline premise removed; S2 and the deployed100-bit target not established.
'''
write_sections('NBV_multiproof_BRIDGE.md','''# NBV multiproof bridge

**OPEN.** '''+common+'''
## Exact domain and restored cuts

Binary Arity::Two, eighteen levels, canonical strictly increasing live indices,
1<=n<=16, physical nodes<=5504; both actual transaction splits. Same idx/val,
node slice and chronological digest log throughout.

- K003/K002: the original K048/K050 arbitrary16-u32 prefix-copy law now PASSES
  with KMX, and the original last-word fixture's wrong-value control FAILS.
  K009/K015 repeat the complete copy/zero suffix/initial n/count candidate on
  actual well_formed admission: PASS / intended FAIL. No native playback
  disagreement under the mitigation. NBM's generated playback is reused read-only.
- K004–006 check actual parent helpers on arbitrary full scratch: exact slice
  pointers, arbitrary selected bytes, one request and unchanged arbitrary reply.
  K014 is the shared32-byte reply negative control, and FAILS.
  K007/K008 check a complete arbitrary-prestate selected-store frame / wrong
  last-byte control. No whole old array is copied into an independent prestate.
- K044/K045, K046/K047 and K048/K049 recheck the inherited paired/supplied/short
  row windows under KMX, with matched selected-value negative controls.
- K023 is one source scan/commit cut; K024 checks local n=w/next-row bounds;
  K025 checks the actual final predicate and root carrier; K039 checks actual
  binary bits1/width2/levels18. These are local cuts, not complete native loops.

NBV_CountInitialization.count_initialized constructs the prefix-copied natural
prestate and consumes NBJ_CountLevels.eighteen, with no supplied final array or
count equation. NBV_CopyComposition supplies KMX window/frame/adjacency laws.
NBE/NBI/NBJ count, source-row/height, branch/log/poststate and frame theorems are
imported through NBJ_Audit; none is reproved or promoted to a native instance.

## Exact remaining members

1. **NativeCountScanPort:** identify the SAME actual native node_count level
   array/n/count at admission and every scan/commit/outer-level boundary with
   the constructed natural prestate/recurrence. Required conclusion: actual
   node_count(Two,&indices[..n]) returns Some(sourceCount18 of that live prefix),
   with its real rejection paths. Copy is repaired; the full typed-carrier and
   control instance remains open. K023's count<=288 and one/two-child group
   premises still need derivation at every reached native prefix (the inherited
   total count bound alone is not that prefix association). Do not silently
   turn this missing caller-domain proof into a new accepted-run restriction.
2. **NativeRowCarrierLift / NativeNodeGatePort:** compose arbitrary full native
   read footprints, physical sibling selection and one-write frames with the
   SAME branch of NBJ_NodeObservation, including untouched arbitrary rows and
   pre-write reads when w<=i. The restored windows are not a separately supplied
   full native execution or an independently chosen reply/log.
3. **NativeVerifyControlPort:** instantiate actual binary row/level control with
   that full gate, including short-node rejection, n=w, eighteen iterations,
   final n/index/root/cursor predicate and ordered rejected prefixes. K024/K025
   and inherited total inductions alone do not construct this native instance.

These are implementation-refinement gaps, not cryptographic assumptions.
U00/runtime SHA/H, valid heap/ABI/library admission and source-to-ELF remain.
See NBV_HANDOFF.md and NBV_ATTEMPTS.jsonl for validation and limits.
''')
write_sections('NBV_keys_BRIDGE.md','''# NBV keys bridge

**OPEN.** '''+common+'''
Domain: SAME57607-byte proof,22 canonical actual query words<262144,
lo0/n10 or lo10/n12, tree0..2,16 packed/sorted keys with exact zero suffix,
832-byte physical openings and six physical slots.

## Checked and reused

K010 proves opening length/pointer on arbitrary full proof bytes and i<22;
K011 proves the selected32-byte window pointer for arbitrary i/w and arbitrary
surroundings. K027's byte observer timed out. Changed K042 installs one32-byte
window at arbitrary physical offset with KMX; it and wrong-value K043 both
TIME OUT. Neither obtains native byte-locality credit; no zero-surrounding
restriction is imposed on callers.

K016/K017 restore actual batch_leaf/private_leaf_hash_with_digest on arbitrary
832 bytes, all three trees, exact tags/part order/length/selected payload/salt
bytes, one digest and unchanged reply: PASS / wrong-reply FAIL. K018/K019
restore the native packed write and selected full-array frame; K020/K021
restore insertion-sort step/return carrier and frame: PASS / wrong-value FAIL.
K022 rechecks one source slot-offset increment; K038 proves both splits'
selected-key opening bounds and folded index<65536 from canonical raw u.

Imported NBI_Keys canonical_query/packed_word/producer_eq, NBI_Sort and
NBJ_Keys.producer_sorted retain the complete constructed model producer/sort
endpoint. NBJ_Address.opening_range and NBJ_WindowCover are reused, not reproved.
NBV frame and KMX composition theorems are value-level facts, not a proof of a
missing Rust memory interpretation.

## Exact open members

- **NativeOpeningAddress/global byte locality:** associate every physical
  borrowed byte of opening(proof,i) with the installed range on the SAME
  arbitrary proof. Pointer/length is now global; the required indexed-load /
  arbitrary-surrounding frame association is not closed by the timed-out
  K027/K042 or by a mathematical window equality alone. Next cut: separate a
  small supplied-slice indexed load/reborrow from the already global address
  law; never repeat the large allocation/window shape unchanged.
- **KeyProducerSortComposition:** identify the native zero16 initialization,
  forward range iterations and insertion-sort return with that SAME actual
  raw22 query allocation, producer and U64 carrier. No final array or sorting
  equation may be supplied independently.
- **PhysicalLeafComposition:** bind actual sorted-key opening/slot bytes to the
  native leaf cut and installed leaf program, including one exact ordered
  request/reply; no separate successful leaf observation may replace the call.
- **NBE_ParserOpeningDomain, actual callers:** tx1 parse_shape/canonical_scan/
  prepare -> Prepared::new -> transcript queries; tx2/tx2_authenticated
  parse_shape -> tx2_common -> resume -> validate_checkpoint_queries. The source
  establishes the intended length/range/unique-query path, but its actual
  accepted-result-to-SAME-Prepared/proof/query carrier instance is not proved
  here. Canonicality is not obtained by the model's modulo262144. TX1 prepare
  and TX2 resume producer joins remain explicit external implementation gaps.

All local raw canonical/index/length premises are reported; none is silently
promoted to a proven every-caller domain. U00 alone cannot discharge these.
''')
write_sections('NBV_batch_BRIDGE.md','''# NBV batch bridge

**OPEN.** '''+common+'''
Domain: SAME proof/Prepared/roots, idx/val scratch and chronological digest log;
both batches, all three trees, exact first-error prefix and rejected calls.

## Checked cuts and limits

K028's combined native leaf/new-row observer TIME OUTS; K029's wrong-salt
control FAILS, which gives no positive credit. Before further combined tree
variants launched, K030–039 were deferred and replaced by smaller independent
cuts. The source hash cut K016 is already mitigated on every tree.

Post-hash K030/K031 decision, K032/K033 new-entry frame/count,
K034/K035 equal-leaf duplicate continuation and K036/K037 unequal-leaf Merkle
rejection pass with matched failing negative controls, on arbitrary native
scratch. These take a reached leaf value; they do not assume a complete
successful leaf traversal or silently construct an independent digest run.
K038 derives selected opening/folded bounds; K039 fixes actual binary arity.

K012 checks count/capacity guard before byte multiplication and exact suffix
geometry. K013 checks local Parse/Merkle/continuation choice on arbitrary scan
and verifier branch results; it is not an assumed accepted scan. K026/K050
recheck one arbitrary physical8-byte conversion/padding word and its negative
control under KMX. NBJ_PaddingPort.physical_scan and NBI total early-stop / frame
inductions remain inherited. K040/K041 re-establish three-root value projection
with a failing wrong-value control, not three native calls.

## Exact open members

1. **NativeBatchLeafTraversal:** join actual sorted producer -> SAME physical
   opening -> native leaf -> post-hash duplicate/new/reject continuation on ONE
   scratch/effect trace. In particular the digest precedes unequal-duplicate
   Merkle rejection and must remain in its rejected prefix. K028 is excluded;
   independently checked hash and post-hash cuts do not by themselves supply
   this concrete same-execution instance.
2. **NativePaddingPort:** bind actual slot/count result and physical
   chunks_exact(8).any closure to the total installed iterator, then exact
   count>capacity/Parse and verifier/Merkle continuation on that SAME native
   execution. Scalar guards, word conversions and a generic total scan are
   predecessors; no final zero-padding or accepted scan law is assumed.
3. **NativeBatchTreeJoin:** consume CLOSED actual count/verifier/key/leaf
   bridges, preserving SAME scratch and log across trees0,1,2 and first-error
   short circuit. Actual batch_merkle must project queries/two roots from the
   SAME Prepared and folded root from the SAME proof. K040 is only projection.
4. The exact multiproof/keys members and actual caller domains remain as in
   NBV_multiproof_BRIDGE.md / NBV_keys_BRIDGE.md; no unrelated unit was held.

No SHA implementation or field multiplication in Kani; no field stub or new
trust item. Conditional closure on U00 is permitted but is insufficient while
these OWN members are open. Do not replace them by new bridge hypotheses.
''')
write_sections('NBV_U09_BRIDGE.md','''# NBV TX2 U09 bridge

**OPEN; not CLOSED-CONDITIONAL on U00.** '''+common+'''
Exact target: proof length57607; batch1/tree0..2; queries10..21 distinct<2^18;
folded duplicates accepted only for equal leaves; at most12 occupied entries
within MAX_BATCH16; exact slot count/padding and eighteen binary levels; ordered
leaf/node digest calls, rejected prefixes and three roots from SAME Prepared /
proof. No first-batch n<=10 restriction is introduced.

## Function coverage and remaining association

| Functions | Checked predecessors / exact remaining group |
|---|---|
| private_leaf_hash_with_digest, batch_leaf | K016/017 restored local hash law; physical leaf / ordered caller join OPEN |
| batch_key_at, batch_keys, sort_batch_keys | K018–021,038 plus imported complete model producer/sort; SAME native producer/return instance OPEN |
| opening, slot, slot_offset | K010/011 global pointers, K022 offset step and inherited bounds; all-byte native opening/slot association OPEN (K027,042/043 excluded) |
| same_batch_index, same_batch_leaf | K030–037 post-hash decision/frame/error cuts restored; whole leaf traversal OPEN |
| Arity::bits/levels/width, index_at | K023/039 and inherited source cuts; Binary Two constants fixed |
| node_count, well_formed | K003/009 copy restored, constructed initialized count theorem and inherited admission/scan/height inductions; NativeCountScanPort OPEN |
| occupied_binary_parent, sibling_binary_parent, root_matches | K004–007,014,025 and mitigated row windows; full native row/control composition OPEN |
| value_at | Only reached in inactive Arity::Eight branch of verify_in_place; no new live binary call obligation or eight-way proof claimed |
| verify_in_place | NativeRowCarrierLift / NativeNodeGatePort / NativeVerifyControlPort OPEN |
| batch_tree, batch_merkle_values, batch_merkle | Full same-scratch leaf/padding/count/verifier joins and three-call root/error projection OPEN |

NBV_CallerBounds.opening_domain and tx2_scratch derive model range/12-entry
bounds without assuming a final array. They do not prove the actual native
caller producer NBE_ParserOpeningDomain. Source audit: tx2 and authenticated
entry both parse_shape before tx2_common; resume validates the actual22 raw
queries before constructing Prepared; tx2_common requires a.next=SPLIT and
passes batch1. A source path audit is not its missing accepted native/cohort
same-carrier theorem. TX1 prepare and TX2 resume producer associations remain
required, not newly adopted trust items.

Named lower dependency retained: **U00**, with runtime sha256=H realization,
exact byte slices passed and reply returned unchanged. No digest value is
proved by Kani. The 02:05 conditional-closure ruling cannot make this unit
conditional on U00 alone until its OWN members above are proved; no extra
hypotheses for its conclusion are added. No XRn_Join kit or stand-in is used.
''')
rows=['# NBV copy and stub table','',f'Exact KMX patch SHA256 `{sha}`. Applied verbatim in NBV_src; KMX functions unchanged.','', 'No field arithmetic is reached or stubbed. The field-stub/emitted-ok theorem requirement is therefore N/A. Digest callback returns are arbitrary runtime replies; their VALUE stays the existing SHA/H realization item.','', '| Cut | Positive | Matched negative | Status |','|---|---|---|---|']
by={r['attempt']:r for r in v['attempts']}
for label,p,n in [('K048/K050 prefix','003','002'),('Admitted complete copy candidate','009','015'),('Parent reply32','004','014'),('Full selected store frame','007','008'),('Leaf grammar/reply','016','017'),('Key write/frame','018','019'),('Sort step/frame','020','021'),('Combined leaf/new row','028','029'),('Post-hash decision','030','031'),('Post-hash new','032','033'),('Post-hash equal','034','035'),('Post-hash unequal','036','037'),('Three roots','040','041'),('Installed opening window','042','043'),('Paired row window','044','045'),('Supplied row window','046','047'),('Short row window','048','049'),('Padding8 conversion','026','050')]:
 a=by['NBV_K'+p]['status'];b=by['NBV_K'+n]['status'];credit='RESTORED LOCAL CUT' if a=='pass' and b=='expected-negative-fail' else 'NO CREDIT'
 rows.append(f'| {label} | K{p}: {a} | K{n}: {b} | {credit} |')
rows+=['','K005/K006 use the same32-byte reply mechanism and KMX configuration as K004/K014; their full-scratch pointer/selected-byte positive checks pass. This does not close a full row carrier or verifier unit. All inherited copy-dependent cuts not explicitly restored above remain suspended and are not used as full-unit credit.','', 'Activated replacements: KMX_copy_from_slice, KMX_copy_nonoverlapping, KMX_clone_from_slice, with generic entry stubbing across reached Copy monomorphizations (u8/u32/u64/byte arrays). No Vec growth/append/realloc is reached by the credited cuts. Preconditions are matching lengths, valid/aligned/nonoverlapping regions and T:Copy; native array/slice bounds and memory checks are checked in each harness.','', 'Lean meanings reused: KMX_CopyMeaning.loop_spec/copy_prefix/copy_frame. NBV_CopyComposition.window_value/opening_frame/adjacent_windows apply them; NBV_CountInitialization constructs the live initialized count carrier. The original KMX native differential / paired controls / standard-axioms audit are imported read-only, not rerun or claimed as universal Rust-to-Lean equivalence.','']
(E/'NBV_STUBS.md').write_text('\n'.join(rows))
summary=v['totals'];base=subprocess.check_output(['git','rev-parse','1672ab0c0a^'],text=True).strip();commits=subprocess.check_output(['git','log','--reverse','--format=%h %s',base+'..HEAD'],text=True).strip()
write_sections('NBV_HANDOFF.md','''# NBV binary batch authentication handoff

**Multiproof, keys, batch and TX2 U09 remain OPEN. No headline premise removed;
target not yet established.** Exact members and statements are in the four
NBV_*_BRIDGE.md reports. '''+common+f'''
## Established and excluded

K048/K050 and the complete admitted copy candidate are re-established under
exact KMX mitigation with failing matched controls. The old pinned unmitigated
verification/native-playback discrepancy is not silently credited as a pass.
No new result disagrees with the retained native playback. Full native parent
pointer/selected-byte and selected-store cuts pass; inherited leaf/key/sort,
post-hash decision/write/duplicate/error, physical padding word and source row
windows are mitigated as listed in NBV_STUBS.md.

New kernel result NBV_CountInitialization.count_initialized constructs the
copied natural count prestate before consuming the inherited eighteen-level
count theorem. NBV_WindowFrame / CopyComposition give disjoint arbitrary-memory
and KMX value composition; CallerBounds derives installed split/opening/12-cell
bounds. All NBE/NBI/NBJ modules are imported through NBJ_Audit, not reproved.
These model/value results are not a completed native/cohort implementation.

K027 (global byte observer), K028 (combined hash/new-row), K042 (changed
installed32-byte window) and K043 (its negative control) TIME OUT at90s.
No credit; no unchanged positive retry, timeout increase or larger cap.
K030–039 were deferred before launch and replaced by independent smaller
post-hash cuts after K028. The K042/K043 pair was preconfigured; the failed
negative control also receives no credit. K001 failed before proof due to
an own module-path omission; L002/L004 are rejected drafts with raw recovery
sorryAx output excluded. Own script repairs are in NBV_REPAIRS.md.

## Validation, budget and exact evidence

**50/50 Kani invocations charged, 7/100 Lean attempts.** Totals:
`{json.dumps(summary,sort_keys=True)}`.
Kani controls are expected assertion failures, not unwinding/memory failures.
Accepted L007 co-import audits all13 new theorem roots with only propext,
Classical.choice and Quot.sound (or subsets). Exact targets, commands, source
revision/hash, dependencies, exit, wall, peak RSS, swap and full axioms output
are in NBV_ATTEMPTS.jsonl and each receipt/stdout/time/source snapshot.
L007: exit0,wall3.6755984309711494s,RSS4399000KiB,swap0,source revision
b2a35f5d1c plus dirty Audit hash in its receipt. Total scoped wall
{v['wall_seconds']}s; maximum peak RSS{v['max_peak_rss_kib']}KiB; all swap0.
This is focused coherent-object validation, not a frozen release manifest replay.

Every run validates441 selected package identities/edges against444 frozen lock
packages, offline, no new tuple or forbidden edge; before/after lock hash stays
5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef.
KMX patch SHA256 {sha}. No LPb passing stage is newly consumed. Runtime digest
VALUE and prepared/resume producer joins are not silently discharged.

All prover jobs were serial, admitted by exit0 AND allowed:true, in unchanged
S2W scopes MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; Lean-M7000;
optimized Rust profiles. No memory kill, cap increase, parallel own scope,
shared infrastructure repair or transport resubmission. The exact219 resolved
Aeneas objects are pinned in NBV_RESOLVED_AENEAS_PINS.json. Shared leaf cache
is read-only; own batch cache is copied from it and retained. KMX's unchanged
object was copied with source/receipt/object hashes in NBV_KMX_IMPORTED_PINS.json.

## Remaining members and stop justification

Native budget is exhausted. No remaining native run is authorized. Spare Lean
cannot turn these missing concrete source associations into proved facts:

1. Count: actual initialized/admitted scan/commit/outer-level typed carrier,
   including each reached scalar domain, still needs a full native instance.
   The copy bug obstruction is repaired and model initialization is constructed.
2. Row carrier / node gate: full native scratch read/write frame and branch/log
   must associate to SAME NBJ_NodeObservation execution, not separate windows.
3. Verifier: consume that concrete row in source levels, n=w and final/error
   continuation, with SAME physical nodes and chronological requests.
4. Opening: global pointers pass, but byte/load/locality bridge remains; both
   changed byte/window attempts time out. Next split is a small indexed-load /
   reborrow law composed with K010, not another huge symbolic proof allocation.
5. Key/sort: actual raw query allocation, zero-array loop and native return
   remain to be associated with constructed producer/sort, with canonicality
   derived from actual TX1 prepare and TX2 resume callers.
6. Leaf traversal: join actual selected physical opening/hash/post-hash
   rejection/continuation on ONE execution; combined K028 is excluded.
7. Padding: actual slot/count/closure and complete iterator/error/continuation
   association is still needed; scalar/word/model scan predecessors are ready.
8. Three trees / U09: compose those real closed callees on SAME Prepared/proof /
   scratch/log; raw root projection alone is insufficient. U00 is retained as
   the permitted named lower bridge, not used to conceal these own open members.

No independent member was held behind an unrelated unit. All three units and
remaining live U09 scalar/helper classes were attempted within the native
budget. Arity::Eight/value_at are not reached by the binary caller; no eight-way
closure is claimed. Further generic conditional wrappers would add the missing
implementation conclusions as hypotheses, contrary to the contract.

## Source, retention and commits

All498 frozen crates/programs/root Cargo files remain byte-identical to4bb3b3f5.
Only NBV Lean modules/evidence are changed in this checkout; harnesses are
scratch-only, retained as patches and receipt snapshots. No shipped/cfg(kani)
source edit here, so no ELF rebuild trigger. Inherited pins, NOT reproduced:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
All runtime/library/heap/ABI/source-to-ELF items, target and metric unchanged.
Final object comparison, cleanup and patch checks are in NBV_FINAL_HOST_PINS.json,
NBV_PIN_COMPARISON.json and NBV_PACKET_CHECKS.json. Own target/tmp removed only
after terminal receipts; private cache retained; no binaries/objects/ELFs in git.
No other worker/session A worktree/candidate, wallet or key touched.

Actual branch codex/cx-native-tx1e-20261028 (brief named20261027); assigned
checkout retained. Commits, before final handoff commit:

```
{commits}
```

No push or merge. Final handoff commit follows.
''')
(E/'NBV_BUDGET_STOP.json').write_text(json.dumps(dict(kani_used=50,kani_limit=50,lean_used=7,lean_limit=100,native_runs_authorized_remaining=0,reason='Native budget exhausted; exact source-association gaps retained in NBV_HANDOFF.md'),indent=2)+'\n')
print('reports written')
