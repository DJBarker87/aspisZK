from pathlib import Path
import json,lzma,hashlib,re,subprocess,collections
E=Path(__file__).resolve().parent
read=lambda n:json.loads((E/n).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
entries=[json.loads(s)for s in(E/'NJL_ATTEMPTS.jsonl').read_text().splitlines()]
counts=collections.Counter(x['attempt'][4]for x in entries);assert counts=={'L':120,'K':60},counts
roots=read('NJL_AUDIT_ROOTS.json')['roots'];gates=read('NJL_GATE_SOURCES.json')
combined=read('NJL_L200/receipt.json');raw=[read('NJL_audit_gate2/'+g+'/receipt.json')for g in['proof0','proof1']];scan=read('NJL_audit_gate2/scan/receipt.json')
assert combined['exit_status']==0 and all(r['exit_status']==0 and r['standard_only']for r in raw)
assert sum(len(r['results'])for r in raw)==len(roots)==164
assert all(r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for group in raw for r in group['results'])
assert scan['exit_status']==0 and not(scan['dangling']or scan['duplicate_owners']or scan['import_mismatch'])
encoded=(E/'NJL_audit_gate2/scan/scan.jsonl.xz.b64.txt').read_text();import base64
payload=base64.b64decode(encoded);uncompressed=lzma.decompress(payload);assert hashlib.sha256(uncompressed).hexdigest()==(E/'NJL_audit_gate2/scan/scan.jsonl.sha256').read_text().strip()
(E/'NJL_GATE2_SCAN.jsonl.xz').write_bytes(payload);(E/'NJL_GATE2_SCAN.jsonl.sha256').write_text(hashlib.sha256(uncompressed).hexdigest()+'\n')
metrics=[]
for n in[200,201,202,203]:
 r=read(f'NJL_L{n:03}/receipt.json');metrics.append({k:r.get(k)for k in['attempt','kind','module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','env']})
audit=dict(status='LOCAL_GATES_PASS_CANDIDATES_AWAIT_NEXT_LEDGER',target_established=False,headline='AspisR1.RPx_Deployed.deployed',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_revision=combined['source_revision'],budgets=dict(authorised={'kani':60,'lean_support':120,'extraction':0},used={'kani':60,'lean_support':120,'extraction':0}),full_combined_audits_used=2,third_audit_allowed=False,combined_import='NJL_COMBINED_IMPORT.lean',combined_sha256=sha(E/'NJL_COMBINED_IMPORT.lean'),compiled_modules=len(gates['passed']),raw_roots=len(roots),raw_equal=True,standard_axioms_only=True,allowed_axioms=['propext','Classical.choice','Quot.sound'],scan={k:scan[k]for k in['modules','dangling','duplicate_owners','import_mismatch','exit_status','wall_seconds','peak_rss_kib','swaps']},fixtures=dict(receipt='NJL_audit/fixtures/receipt.json',all_eight_pass=True,same_binaries='NJL_GATE2_BINARIES.json',repeat='Not rerun: hardened walker/driver/C unchanged; only source selection and strict current-attempt receipt metadata changed.'),scope_policy=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000,one_scope_at_a_time=True,admission='Every actual launch requires reservation allowed:true AND exit0; each attempt retains admission JSON',optimised_offline_rust=True,cargo_target_dir='/home/dombarker/project-offloads/codex-cx-terminal2-20261108/NJL_target (removed only after export)'),final_gate_receipts=metrics,gate1='NJL_GATE1.json',raw_receipts=['NJL_audit_gate2/proof0/receipt.json','NJL_audit_gate2/proof1/receipt.json'],native_pairs='NJL_NATIVE_PAIRS.json',export='NJL_EXPORT.json',trust='P6/D188 native semantic transport option A RECLASSIFICATION only; no trust added or removed; no pending RuntimeCpiReadonlyEntry7 use',ledger_credit='Waits for the next authoritative ledger gate; no authoritative ledger edited')
(E/'NJL_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
(E/'NJL_GATE2.json').write_text(json.dumps(dict(status='PASS',combined='NJL_L200',raw=['NJL_L201','NJL_L202'],scan='NJL_L203',source_revision=combined['source_revision'],compiled_modules=len(gates['passed']),raw_roots=len(roots),all_standard_axioms=True,scan_modules=scan['modules'],dangling=0,duplicate_owners=0,import_mismatch=0,full_combined_audits_used=2),indent=2)+'\n')
packet=read('NJL_CLOSED.json');packet.update(status='LOCAL_GATE_PASS_AWAIT_LEDGER',admission='Gate2 combined NGK+NIU+NJB+NIX+NJL+RPx_Deployed passes; raw ax2 standard only; NFX scan exit0; no authoritative promotion until next ledger gate',validation='NJL_AUDIT.json',local_gate='PASS_GATE2',credit_waits_next_ledger_gate=True)
for r in packet['functions']:r['local_gate']='PASS_GATE2';r['authoritative_status']='UNCHANGED_PENDING_NEXT_LEDGER'
(E/'NJL_CLOSED.json').write_text(json.dumps(packet,indent=2)+'\n')
# Print the actual compiled ROOT TYPES and explicitly inventory permitted hypotheses.
root_text=['# NJL compiled root statements and (aq)(2) hypothesis inventory\n','Target not established. Statements below come from successful scope stdout, not a reconstructed statement. Generic SUPPORT domains never become root premises. `(lookup : Cut)` on214 is the reviewed native lookup transcription admitted by(ai)(5); its bounded weight is supplied by the same-link caller_weight theorem.\n']
for r in packet['functions']:
 owner=r['owner_module'];attempt=gates['passed'][owner];s=(E/attempt/'stdout.log').read_text();name=next(n for n in r['lean_roots']if '.'+owner+'.'in n)
 match=re.search(r'theorem '+re.escape(name)+r'\s*:(.*?)(?:\s:=\s*\n)',s,re.S);assert match,name
 root_text+=['## '+','.join(r['rows'])+' — '+name+'\n','Permitted input/domain inventory: '+r['root_domain']+'. '+r['premise_policy']+'. Derived child Packets, traces and successful Results are conclusions, never root hypotheses.\n','```lean\ntheorem '+name+' :'+match[1]+'\n```\n']
(E/'NJL_ROOT_STATEMENTS.md').write_text('\n'.join(root_text))
# Preserve authoritative frozen ledger identities and source correspondence categories.
basep=E.parent/'ledger13-20261107/NIU_LEDGER.json.xz';baseline=json.loads(lzma.decompress(basep.read_bytes()));baseline_rows={r['row']:r for r in baseline['rows']};ownrows=sorted(row for r in packet['functions']for row in r['rows']);assert len(ownrows)==12
for r in packet['functions']:
 for row in r['rows']:assert r['frozen_body_sha256']==baseline_rows[row]['frozen_body_sha256']
delta=dict(baseline='evidence/ledger13-20261107/NIU_LEDGER.json.xz',baseline_sha256=sha(basep),baseline_counts=baseline['counts'],proposed_rows=ownrows,new_own_packet_count=12,reused_existing_candidates=['TX1:215','TX1:268'],reused_credit='Not new NJL work: read-only NIX_ResidualCut/ResidualLog and NJB_SemanticPublic.result; same final combined/raw/scan admission',local_gate='PASS_GATE2',authoritative_ledger_edited=False,credit_waits_next_ledger_gate=True,proposed_only_counts_if_own12_admitted={'CLOSED':444,'QUALIFIED':0,'OPEN':155,'total':599},proposed_only_counts_if_own12_plus_both_reused_admitted={'CLOSED':446,'QUALIFIED':0,'OPEN':153,'total':599},counts_note='Hypothetical arithmetic against baseline13 only; neither count is an authoritative ledger claim',target_established=False)
(E/'NJL_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
remaining={
'TX1:218':'Actual parent/source-order/abort and136-endpoint frame induction still needed. Direct children208/214/215 are available;220 and223 remain OPEN. No child-success or endpoint-equality premise is admissible.',
'TX1:220':'Full tensor finish must consume actual217/219 packets and dispatcher225 on every source arm.225 count2/3/4 has OPEN out-of-slice040/041/043; cannot restrict callers to count1. Parent source cut/whole-tensor association also unfinished.',
'TX1:223':'NativeK055/K056 deployed forwarding is available. Complete224 child Result/cohort association is missing; then compose same opened16/lambda and full14reply. Do not substitute the nondeployed literal arm.',
'TX1:224':'Powers8, actual std8map9word caches, all mutable8cell frames and complete8step windows with internally derived domains compile (WindowPowerArray L119, CachedWindow L112). Next: compile UNCOMPILED same-packet join sketch WindowInvocation.lean.txt; derive14tail actual field Results on that SAME packet, compose existing NJB_K104..131 with K053/05414cell frame, and prove exact adopted pattern-literal/tuple meaning. K049/050 map and K051/052 four-window capture bindings are complete native SUPPORT. Remaining known work is Lean-only, not a Kani stop.',
'TX1:225':'SLICE BOUNDARY: count2/3/4 call OPEN field helpers040/041/043 outside this job list. Count1 does not cover callers. Field multiplication in Kani is forbidden. Await CLOSED actual callee bridges; do not author out-of-slice proofs or strengthen caller preconditions.',
'TX1:232':'REAL direct child is260 plus CLOSED230 twice at starts0 and16; not228/229/233. Need actual tuple arrays from260, source-ordered calls/full24frame, complete Result/cohort root.260 remains OPEN.',
'TX1:233':'231 is now ready at N33/start49. Need actual four selector-row calls, three10-bit range loops over z/succ_z/xor12_z, actual reconstruct_10/mul_m311024/1048576 results, residual slots30..32, two conservation terms, preweighted at82, full33/24frames and adopted Result. Native parent/caller-domain composition remains, not an unrelated-callee block.',
'TX1:234':'K057/058 arbitrary actual group covers source lift/sub/pack/prepared-product operands, nine cachewords, offsets and right-group1 tweak position. Still derive actual Prepared::new(high), expected empty_root239 versus frontier and canonical domains, complete both groups and zero opposite pair, level<20 shift, full two-array cohort Result. Lift243/pack039/field callees are CLOSED; no invented external OPEN callee. Lean arithmetic/group/root composition remains.',
'TX1:235':'K059/060 actual arbitrary level<20 step now available: same u64 index/frontier[level]/opened16/high[34+level], four child replies/adds/full4state and level+1; extra K063 corrupt-u64 control FAILS. Need CLOSED234/domain discharge and finite20-level ZERO-initialized induction plus full cohort Result. Never rerun full buffers or unchanged windows.',
'TX1:237':'Depends on OPEN218/261 and out-of-slice OPEN308 evaluate_state_only_poseidon_oracle_projected. Need source-ordered terminal/base composition and full Result; no successful-child hypothesis.308 is a slice-boundary finding, not an authorized new proof target.',
'TX1:242':'Earlier NJB_K054 andK060 timed out; excluded, never rerun. Atomic residual/pack/prepared pairs exist, but source requires ALL8subtractions before both products. Need that global-order frame, actual constructor, full two-cell return and adopted cohort root. Independent ready Lean/native composition remains; not blocked by an unrelated member.',
'TX1:245':'Branch-only carry<20/zero observation is not true-body arithmetic. Need actual constructor, all8same residuals, both packs/products and full2cell cohort Result. K057/058 left-group window may be reused only after same-argument/domain proof; no opaque body-reply credit.',
'TX1:246':'K061/062 now binds actual Some constructor high, SAME9word cache to both groups, expected/opened inputs, two replies, and None ZERO. Need same-input canonical expected/high domains, actual arithmetic group Results (K057/058 left-window), finite two-group frame and full cohort Result. Option<Digest> is data only, no Option<fn> or contracts. Generic fields/constructor laws do not replace the missing arithmetic body.',
'TX1:250':'Wrapper consumes OPEN251; needs actual source domain and full output/cohort assembly on same public inputs. No independent output or acceptance-only hypothesis.',
'TX1:251':'Direct children235/242/245/246 remain OPEN. Need all actual public/append arguments and canonical bounds, source-global branch/call order and complete mutable/returned arrays, consuming CLOSED callee packets when available.',
'TX1:260':'227 is ready. Need actual initial-lane source/selector/public prefix and full initial16/absorption16 tuple, internally prove each child domain, preserve source order and abort frames, and associate complete emitted cohort Result. No unrelated OPEN member is required; work stopped only at the hard allocation limit.',
'TX1:261':'Actual deployed children228/229 ready;232/233/250 remain OPEN. Need source-ordered five packed24 mutations, every actual child/domain, return/abort frame and cohort Result. No bypass via success hypotheses.',
'TX1:263':'Consumes OPEN237 plus actual equality/terminal children. Need full parent invocation, domains, return carrier and error frames. Headline remains unestablished.'}
order=read('NJL_ORDER.json');lines=['# NJL remaining work — final\n','Target not established. Both allocations are exhausted:60/60Kani,120/120Lean/support,0/0extraction. Final audit2/2 PASSED:164raw roots standard-only,15199modules scanned with zero errors. Twelve new complete row packets await the next authoritative ledger gate;215/268 are read-only predecessor candidates. No authoritative ledger edited.\n','No further formal launch is authorized. This is not Kani-only exhaustion: Lean-only224 and other independent obligations were pursued through the last focused scopes, then the reserved final4audit scopes. Every remaining row below states its actual obligation.\n']
owned={row:r for r in packet['functions']for row in r['rows']}
for r in order:
 row=r['row'];lines.append('## '+row+' '+r['function'].split('::')[-1]+'\n')
 if row in owned:lines.append('Complete new NJL packet; local combined/raw/NFX gate PASS. Root: `'+next(n for n in owned[row]['lean_roots']if '.'+owned[row]['owner_module']+'.'in n)+'`. No remaining local row proof; credit awaits authoritative ledger gate.\n')
 elif row=='TX1:215':lines.append('Consumed NIX candidate read-only: NIX_ResidualCut.packet and NIX_ResidualLog.packet, copied hashed retained objects; included in both raw groups/final combined. No redo, no new NJL credit. Next ledger admission only.\n')
 elif row=='TX1:268':lines.append('Consumed NJB_SemanticPublic.result read-only; included in final combined/raw/NFX. No redo or new NJL credit; next ledger gate only.\n')
 else:assert row in remaining,row;lines.append(remaining[row]+'\n')
 if r['children']:lines.append('Real in-job direct dependencies: '+', '.join(r['children'])+'.\n')
lines+=['## Outside scope\n','TX1:256 remains NJG-owned and untouched. OPEN field040/041/043 and oracle308 are slice boundaries. No new trust row, pending RuntimeCpiReadonlyEntry7, XRn kit or stand-in was used.100-bit PER-ATTEMPT, privacy and two-transaction requirements are unchanged.\n']
(E/'NJL_REMAINING.md').write_text('\n'.join(lines))
# Native/source register: authoritative NDT body hashes checked above; historical
# erasure snippets may hash a broader signature-inclusive span, never substituted.
correspondence={
'TX1:208':'Frozen active wrapper delegates to209; reuse NJB_K044/045 exact same Selectors/reply.',
'TX1:209':'Predecessor high/low arithmetic windows and mask registry; NJL_K004/002 retains high64 then low7 guards/increments/zero initializers. CONTROL_ERASURE broader signature-inclusive span is provenance, authoritative NDT body hash is separate.',
'TX1:214':'Genuine136link index+side only; K019/020 direct literal gc/pc payloads match shared generated Lean tables; K015/016 one arbitrary103cell write preserves kind/operand/full frame. Two disjoint writes composed; caller_weight proves same-link binary domain.',
'TX1:216':'Frozen block/tag272 andoffset31 literals checked by K028/027; K029/030 one min(index+4,end) chunk and031/032 init/exit; NJB066..071 actual read/raw/reduce steps; K025/026 actual four-word constructor. Finite take4/drop4 schedule and exact-field sum proved in Lean.',
'TX1:217':'Actual deployed tag-dot arm; K035/036 same immutable selectors borrow/coordinate/unchanged full reply; scratch ignored.216 actual clause internally supplied.',
'TX1:219':'NJB036..039 exact inner and outer source windows; K017/018 frozen four-group26coordinate control. Immutable borrowed patterns pointer is SAME input identity only, never independent-byte equality. Full raw4state and sparse weighted meaning.',
'TX1:227':'NJB040/041 and046/047 actual nine-word prepared prologue/lane windows; K005/006 actual std16callback. Same3constructed caches and all16returned lanes compose to adopted absorption literal.',
'TX1:228':'K037/038 exact rows1017/1018, expected typed variant, same opened16, actual12child lanes into preweighted0/full24reply. Constants use retained symbolic theorems; all child Results internally supplied.',
'TX1:229':'K043/044 actual THREE-view Openings (old16token K039/040 excluded), exact57..63 range, low1/5/9/13, three adds/product, actual17child lanes into preweighted32/full24reply. Children internally supplied.',
'TX1:231':'Deployed N33/start49 monomorph only. NJB048..053 gather/group/native4operation frame/control; K033/034 actual std4callback. Full24canonical carrier equals actual adopted preweighted on internally built33same-selector products.',
'TX1:244':'Reused native context/head/arbitrary digestlane/tail with actual9word Prepared; finite8digest writes and disjoint4scalar slots/full12array. Arbitrary canonical occupied, no bit restriction. Exact adopted occupancy literal Result.',
'TX1:247':'Native head and split one-side source windows (timed-out combined shapes excluded), actual caches, all8unrolled left/right pairs, head+16writes/full17array. Arbitrary canonical bit; exact adopted path literal Result.'}
source_rows=[]
for r in packet['functions']:
 row=r['rows'][0];source_rows.append(dict(row=row,function=r['function'],ndt_body_sha256=r['frozen_body_sha256'],frozen_release=packet['frozen_revision'],native_pairs=r['native_pairs'],association=correspondence[row],proof=r['lean_roots'],trust='(aq)(5) direct source/native interpretation under retained P6/D188 tool trust; RECLASSIFICATION, no trust removal'))
(E/'NJL_NATIVE_TO_SOURCE.json').write_text(json.dumps(dict(ndt_baseline=delta['baseline'],rows=source_rows,scope='Exactly12candidate rows; SUPPORT windows and broader erasure spans are not row admissions'),indent=2)+'\n')
# Refresh production source identity without invoking any build.
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();ship=read('NJL_SHIPPED_CHECK.json');ship['branch_revision']=rev
for r in ship['trees']:
 r['branch_tree']=subprocess.check_output(['git','rev-parse','HEAD:'+r['path']],text=True).strip();assert r['branch_tree']==r['frozen_tree'];r['byte_identical']=True
assert not subprocess.check_output(['git','diff','--name-only','HEAD','--','crates','programs'],text=True)
ship['final_note']='No repository shipped source or cfg(kani) harness module was edited; all harnesses scratch-only patches. No ELF rebuild triggered; unchanged predecessor pins retained, not represented as newly rebuilt.'
(E/'NJL_SHIPPED_CHECK.json').write_text(json.dumps(ship,indent=2)+'\n')
print(json.dumps(dict(status=audit['status'],candidate_rows=len(ownrows),raw_roots=len(roots),scan_modules=scan['modules'],scopes=dict(counts))))
