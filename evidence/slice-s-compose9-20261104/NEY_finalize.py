"""Report the final checked checkpoint without repeating an unchanged replay."""
from pathlib import Path
import json,datetime,subprocess,hashlib,re
E=Path(__file__).resolve().parent;R=E.parent.parent
read=lambda p:json.loads(p.read_text())
status=read(E/'NEY_STAGE_STATUS.json');assert status['closed_rows']==86 and status['edge_closed']==110
rows=read(E/'NEY_CHECKED_ROWS.json');packet=read(E/'NEY_LEDGER_DELTA.json')
old=read(E.parent/'slice-s-compose8-20261104/NEX_STOP_AUDIT.json')
closed={r['function'] for r in rows if r['composed_status']=='CLOSED'}
changes={
'WideExact::to_limbs':'K148/K149 prove the actual getter only on values constructed by from_limbs from canonical limbs. The selected NBG packet covers all raw eight-word carriers. This stronger new precondition is NOT established by every incoming caller, so it cannot discharge NCS_R074.PacketDomain. Need a full-domain native contract/carrier certificate with matched controls; no claim from the canonical-only probe. K147 compilation failure is excluded.',
'Variant::tag':'K150/K146 observe all three actual native enum constructors under deployed features with a failing value control. This is a local probe, without the selected NCS_R080 physical/extracted cohort/native contract certificate and per-call carrier association. Existing NBG_Transport.tag_result is reused. A new Lean model case split cannot supply the missing native certificate.',
'WideExact::to_le_bytes':'The actual caller/self raw carrier, selected to_limbs input domain, native ordered return buffer and copy/loop association remain unbound. The to_limbs canonical-only probe does not cover the selected raw domain. Reuse existing byte and induction laws; need native arbitrary-window/step certificates and matched controls.',
'decode_pool_v1_pair_forest_terminal_request_v1':'K133/K134 close the isolated actual four-byte slice/array magic comparison and K135/K136 the isolated zero32 comparison, with failing controls. Still need the full 320-byte request record field/window join, exact payment child slice/domain/Result/error path and original parent call/order/frame association; isolated comparison checks are SUPPORT ONLY.',
'asq8_common':'K137 full typed aggregate check reached the outer 180-second timeout and receives no credit. K138–145 isolate four exact source RHS projections with matched controls; they do not prove the original full Box allocation, unread-field frame or all fifteen common coordinates. Need small native projected-read/owned-write certificates covering all fields, then existing Lean record/frame join. Never repeat the timed-out aggregate shape.',
'reconstruct_asq8_statement':'Constructor children and the full raw/adopted model/domain laws are inherited. Native common association remains OPEN (K137 timeout); native 64-bit guard and common/constructor continuation owned-carrier/Result/order frame also remain unbound. Four isolated RHS checks do not close the fifteen-field common or the original root.',
'scan_proof_buffer':'Need the SAME 688-byte header and child Result/Box frame, exact byte696 tag association, and native compiler/library equality-to-iteration association. K150/K146 tag observations do not identify this root callsite/carrier. Existing equality-step/Lean induction and afterstate child bridges are reused; no whole-buffer replay is proposed.',
'emit_result':'Binding validator and nine-window result encoder are now CLOSED members. NEY_EmitComposed.result_state_effects discharges their MODEL bridges and derives the reached same-statement encoder domain. The original native emitter still lacks an efficient split certificate for the owned 792-byte Ok return-to-send continuation, same payload/order/guard and exact child arguments. K129–132 timed out and are excluded. Do not assume the root bridge. RuntimeReturnData under (ab) is ADDED trust, supporting model only; zero new CLOSED native uses.'}
members=[]
for m in old['members']:
 if m['function'] in closed:continue
 key=next(k for k in changes if m['function'].endswith(k))
 related=[r for r in rows if r['function']==m['function']]
 m.update(exact_remaining_obligation=changes[key],lean_only_obligation_remaining=False,why_more_Lean_alone_is_insufficient='The existing mathematical/cohort, range, record/frame and induction facts are already proved or reused. The remaining certificate needs the actual frozen native body, full selected domain/carrier and/or callsite argument/Result/effect witness. A local probe or another model equality cannot supply that native evidence. No independent missing pure Lean lemma is identified.',open_call_domains=[o['id'] for r in related for o in r['caller_domain_obligations'] if o['status']!='CLOSED'])
 members.append(m)
assert len(members)==8
kani=list(E.glob('NEY_K*/receipt.json'));lean=list(E.glob('NEY_L*/receipt.json'));assert len(kani)==150 and len(lean)==42
stop=dict(target='not yet established',closed_rows=86,total_rows=97,closed_edges=110,total_edges=129,closed_roots=3,total_roots=7,kani_used=150,kani_limit=150,lean_used=42,lean_limit=60,whole_budget_fraction=192/210,unused_lean_slots=18,stop_reason='Native allowance exhausted; all eight remaining members require new native evidence as individually recorded, with no outstanding independent Lean-only obligation. 91.43% of the combined allowance used.',members=members,timeout_finding='NEY_TIMEOUT_FINDING.json',new_closed_ab_uses=0)
(E/'NEY_STOP_AUDIT.json').write_text(json.dumps(stop,indent=1)+'\n')
receipts=[]
for p in sorted(kani+lean):
 d=read(p);receipts.append({k:d.get(k) for k in ['attempt','kind','module','command','native_command','sources','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_tree_dirty','source_hashes','print_axioms','limits']})
(E/'NEY_SECTION6_RECEIPTS.json').write_text(json.dumps(dict(frozen_native_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',measurement_classification='exhaustive finite native checks and formal model theorems; not a new soundness bound or release proof',results=receipts),indent=1)+'\n')
# Every conservative edge stays in the inventory, including unresolved alternatives.
edges=read(E/'NEY_EDGES.json')
for e in edges:
 if e['status']=='OPEN':e['obstacle']=next(m['exact_remaining_obligation'] for m in members if e['edge'].split(' -> ')[0]==m['function'])
(E/'NEY_EDGES.json').write_text(json.dumps(edges,indent=1)+'\n')
oldmd=(E.parent/'slice-s-compose8-20261104/NEX_COMPOSED.md').read_text()
text='''# Slice S composition checkpoint

**86/97 rows, 110/129 internal edges, 3/7 roots CLOSED. The seven-root target is not established.** Baseline NEX:82/97,93/129,2/7. Authority: NEY_ENCODER_VALIDATION.json, NEY_LEDGER_DELTA.json, NEY_CHECKED_ROWS.json and the unchanged inherited validator chain. All 24 mutation/validation tests pass (NEY_ENCODER_TESTS.log).

Frozen native revision4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; headline AspisR1.RPx_Deployed.deployed, frozen3, L154 parameter, D188 narrowed. No shipped file changed. ELF rebuild was not triggered. Native composition is ruling(y)'s hybrid: a kernel MODEL theorem plus checked actual frozen caller/child/domain certificates, never a claimed kernel theorem directly over Rust source. P6/D188 optionA is trust reclassification. Approved NDT trust rows and RuntimePersistence remain unchanged.

Every CLOSED root's ONLY qualifications are its own PacketDomain and PhysicalInterpretation, approved trust rows/RuntimePersistence and CompositionTrustOptionA. No callee PacketDomain/PhysicalInterpretation is retained as a root hypothesis. Same inputs, canonical carriers, prestate, complete Result including errors and ordered effects are checked at each actual callsite. Certificate edge classifications are in NEY_LEDGER_DELTA.json; all129 edges, including conservative alternatives, remain listed in NEY_EDGES.json.

RuntimeReturnData under(ab) is ADDED runtime trust, used only by supporting emission MODEL facts here. **New CLOSED native(ab) uses:0.** This does not prove runtime readback. No new function-pointer or writable-static pass is credited or quarantined; inherited quarantines remain unchanged.

## decode_public_statement_box — CLOSED

The native root forwards the same live bytes to the now-CLOSED terminal decoder, preserves each child error mapping, and returns the cohort value in the same freshly allocated Box. K054–105 independently observe all26 fields; K106 rejects wrong allocation and K107 rejects a corrupted child reply. The terminal certificate uses K001–052, K053 and the inherited length gate; L005/L006/L009–032 bind all coordinates, and L035 fixes header/kind/payment-window geometry. No inner named hypothesis remains.

Kernel MODEL theorem `NEX_PublicModel.result_state_effects` (NEX_L032):

```lean
'''
public=next(c for f,c in packet['NEY_certificates'].items() if f.endswith('decode_public_statement_box'))
model=next(t for t in public['domain_theorems'] if t['name']=='NEX_PublicModel.result_state_effects')
text+=model['statement']+'\n```\n\n#print axioms:[propext, Classical.choice, Quot.sound], pinned in NEX_L032. Coherent installed endpoint is op47. Root qualifications are listed above; (ab) uses:none.\n\n'
for name in ['validate_pool_v1_pair_forest_terminal_statement_v1','encode_pool_v1_pair_forest_terminal_statement_v1']:
 title='## crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::'+name
 start=oldmd.index(title);end=oldmd.index('\n## ',start+len(title));text+=oldmd[start:end]+'\n\n'
text+='''## Newly CLOSED non-root members

The terminal statement decoder, binding validator and result encoder are newly CLOSED. Binding K109/K110 preserves both child Results/arguments/order at the derived record; L004/L007/L040 derive the reached same-statement domain. Encoder K111–128 covers nine disjoint windows, with matched corruption controls and exact child arguments/Results. L002/L008/L037–040 join the actual KMX writes into the cohort792-byte stores and payload. This closes4 additional rows and17 additional edges; no OPEN emitter is promoted from its child closures.

## OPEN root obligations

No complete native composed theorem is established for the following roots. Missing native bridges are explicit obligations, never hidden premises or a self-assumed root bridge.

'''
roots=['decode_pool_v1_pair_forest_terminal_request_v1','emit_result','reconstruct_asq8_statement','scan_proof_buffer']
for short in roots:
 m=next(m for m in members if m['function'].endswith(short));text+='### '+short+' — OPEN\n\n'+m['exact_remaining_obligation']+'\n\nExplicit unbound call-domain obligations:\n\n'+''.join('- `'+s+'`\n' for s in dict.fromkeys(m['open_call_domains']))+'\n'
text+='''## Supporting emission MODEL theorem

`NEY_EmitComposed.result_state_effects` has no free BindingBridge/EncoderBridge hypothesis. This completes the Lean continuation; it does not replace the missing actual native emitter certificate. Full statement:

```lean
'''
s=(E/'NEY_EmitComposed.lean').read_text();a=s.index('theorem result_state_effects');z=s.index(' :=',a);text+=s[a:z]+'\n```\n\n#print axioms:[propext, Classical.choice, Quot.sound], NEY_L041 and aggregate NEY_L042. The reached encoder domain is derived from successful binding on the SAME statement, never an extra root precondition. RuntimeReturnData remains an explicit ADDED trust item for a future native(ab) closure.\n\n'
text+='''## Audit and limits

NEY_L042 imports36 accepted modules and prints axioms for50 theorem references. Exit0,wall2.200257s,peak5312644KiB,swap0; revision856586302a119162e4181e314d8c6c3ba857a243 with dirty source snapshots pinned. All axioms are a subset of[propext,Classical.choice,Quot.sound]. Exact targets, status,time,RSS,swap,revision,source hashes and axioms for every run are in NEY_SECTION6_RECEIPTS.json and individual receipts. Failed elaborations/compilations/timeouts are retained and excluded.

Budget150/150 Kani,42/60 Lean,192/210 combined(91.43%). NEY_STOP_AUDIT.json lists all eight remaining members and why further Lean-only work cannot supply the missing native evidence. K129–132 and K137 timed out, with no credit. The controller submitted three emission controls before review of the initial timeout; this sequencing violation is recorded in NEY_TIMEOUT_FINDING.json. No further unchanged timeout shape was run after review; caps/timeouts were never raised.

K148/K149's canonical-only getter probe is narrower than NBG's all-raw carrier domain: it is a finding and earns no composed credit. K150/K146's all-variant tag observation and K133–136's request comparisons are supporting checks, not complete selected domain/physical/native contract certificates. K138–145 are explicitly source-isolated RHS checks, not an original whole-aggregate proof. No multiplication was checked in Kani.
'''
(E/'NEY_COMPOSED.md').write_text(text)
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
checks=[]
for ref in ['codex/cx-slice-s-leaves-20261029']:
 r=subprocess.run(['git','log','-3','--oneline',ref],capture_output=True,text=True);checks.append(dict(ref=ref,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))
(E/'NEY_LEAF_BRANCH_FINAL_CHECK.json').write_text(json.dumps(checks,indent=1)+'\n')
(E/'NEY_HANDOFF.md').write_text('''# NEY slice S handoff

Validated checkpoint:86/97 rows,110/129 edges,3/7 roots CLOSED. Seven-root target NOT established. Baseline82/97,93/129,2/7. Read NEY_COMPOSED.md, NEY_STOP_AUDIT.json, NEY_EDGES.json and NEY_LEDGER_DELTA.json first. Exact new certificates: terminal decoder, public root, binding validator and result encoder. No re-proof of inherited bridges. All24 validator tests pass; immutable NEX baseline gates remain mandatory.

Branch codex/cx-slice-s-compose9-20261104 was preexisting and preserved (requested old branch differed). Only NEY-prefixed evidence files changed. No push, shipped Rust/Lean changes, wallet operations or ELF rebuild occurred. Headline/frozen3/L154/D188 and 100-bit per-attempt/privacy/two-transaction contract remain unchanged. P6/D188 optionA is reclassification; RuntimeReturnData(ab) is ADDED trust, supporting model only,zero newly CLOSED native uses.

Native budget150/150; Lean42/60. All192 runs and failure receipts retained. No independent missing Lean-only lemma is identified for the eight remaining members; each needs the exact native/domain/carrier witness listed in NEY_STOP_AUDIT.json. K129–132 emitter timeouts and K137 common timeout are excluded; the controller's submission-before-review violation is in NEY_TIMEOUT_FINDING.json. Do not repeat these whole-record shapes. New common RHS probes are SUPPORT ONLY. Canonical-only to_limbs does NOT discharge the selected all-raw domain; tag probes lack the full selected native/extracted physical certificate.

Use the same host workspace /home/dombarker/project-offloads/codex-cx-slice-s-compose9-20261029 and retained cache /home/dombarker/project-offloads/codex-cx-slice-s-compose9-cache-20261029. NEY_FINAL_CACHE.json pins the copied accepted objects/sources (NEY_final_objects_20261104), original and destination hashes and owned rebuildable target/tmp cleanup. Cache never deleted; no key cleanup. NEY_HOST_PINS.json records imported predecessor hashes, NEX accepted objects first. Each Lean receipt pins the exact LEAN_PATH-selected objects and Aeneas objects.

No native/Lean job or controller remains active. One scope at a time was used, admission required allowed:true AND exit0. Caps6G/8G/Swap0/Tasks64,Lean-M7000; optimized Rust; no cap or timeout increase. Frozen graph/offline lock and post-run hash checks are per attempt. Exact KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; complete copy-dependent credited sets have failing controls. No writable-static or function-pointer-dependent credit added.

Authoritative replay: NEY_ENCODER_VALIDATION.json and NEY_ENCODER_TESTS.log. Avoid repeating the unchanged full replay. Final L042 axioms audit checks50 theorem references from36 modules,standard axioms only. NEY_SECTION6_RECEIPTS.json supplies exact target/status/wall/RSS/swap/revision/axioms. NEY_finalize.py only reports the accepted checkpoint; it does not promote rows. NEC branch could not be resolved locally; final git-log error is retained in NEY_LEAF_BRANCH_FINAL_CHECK.json. Do not fetch or touch session A worktrees.
''')
print(json.dumps(dict(closed_rows=86,closed_roots=3,open_members=len(members),kani=150,lean=42,report_source_revision=revision)))
