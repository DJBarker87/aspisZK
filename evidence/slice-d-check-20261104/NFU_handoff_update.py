"""Generate interruption-safe member-by-member handoff from admitted statuses."""
from pathlib import Path
import json,collections,subprocess,lzma
E=Path(__file__).resolve().parent;R=E.parents[1]
J=lambda p:json.loads(p.read_text())
closed=J(E/'NFU_CLOSED.json');cf={f['function']for f in closed['functions']};ledger=json.loads(lzma.decompress((E/'NFU_COMPOSED_LEDGER.json.xz').read_bytes()));by={r['row']:r for r in ledger['rows']}
receipts=[J(p)for p in E.glob('NFU_*/receipt.json')];counts=collections.Counter(r['kind']for r in receipts)
used=dict(kani=counts['kani'],lean_support=sum(r['attempt'].startswith('NFU_L')for r in receipts)+int((E/'NFU_L047-queue.log').exists()),extraction=counts['extract'])
reasons={
'slot_offset':'Independent small helper still needs full native all-offset/row Result and overflow/error/frame certificate plus canonical model port. No prior horizontal packet was reclassified as closure. Needs fresh Kani and Lean/audit budget.',
'expand_semantic':'K042/K043 cover only invalid semantic/output lengths. Valid path still needs the exact original-row iteration schedule, expand_values SAME output-window domain, expansion offsets/frame/disjointness and canonical source/model induction. The CLOSED expand_values child does not close this caller. Needs native schedule and model/audit work.',
'decode_k':'Needs exact ValidatedRecord row/framed caller-established domain, original payload windows, N=1/28/29 canonical field decoding, all errors and returned array/frame association. Getter closure is insufficient. Needs native decoder and Lean/substitution/audit budget.',
'parse_record':'K044..049 give invalid-row/length/tag guard pairs; K015/K063 isolate bad-header return with assert-false unreachable validator. Valid-header path, borrowed token provenance, complete exact errors and validate_record_fields substitution remain OPEN. E001 is a reduced-carrier reference only (NFU_REFERENCE_CARRIER_FINDING.md). Needs native valid branch plus full-error model transport/audit.',
'parse_record_at':'K021/K053 prove short-get returns before parser. Long-get path needs checked add/get and SAME original slice/result/error forwarding through parse_record. E002 extraction is reduced-carrier only. Needs native caller valid branch and parser packet/model association; no full-buffer replay.',
'new':'Accumulator::new TX1:174 depends on OPEN heap::filled outside this assignment; no allocation/value/error/frame packet exists. Record this slice-boundary obligation before any caller closure (NFU_BOUNDARIES.md). Requires that external native/Lean packet and native initialization/model join.',
'checkpoint':'KNE 116-transition schedule/native_result is reusable but DriverEstablishedDomain is not proved at this call site: SAME p/a preparation provenance, S2, weights64,22 indices<262144, canonical fields and a.next=10. Preparation is outside NFU, query loop belongs to NFS, field writers to NFT. Need exact incoming-state domain derivation plus all remaining real callee packets; no free accepted-run hypothesis.',
'finish_query_dot':'K072/K073 and the remaining finish_g observation pairs are a typed arbitrary-prestate one-step candidate with unconstrained push reply/nine-word receiver mutation; see NFU_FINISH_CANDIDATE.json. NFG push is CLOSED on canonical E/valid receiver and arbitrary raw scalar/count. Still needs frozen source-erasure/typed-cohort transport without legacy FIo, one loop induction with abort prefixes, new/finish association and final aggregate bounds/caller domain. E003 does not prove those joins. Requires additional native association and Lean/audit budget.',
'snapshot':'Needs actual account data borrow/length/owner/key/errors, exact byte copy and full Vec allocation/cleanup/frame/provenance. Existing source dependencies and copy/fidelity shapes are not assumed; needs one-window KMX controls/Lean frame composition and full record/error model.',
'data':'Needs complete actual borrowed data Result/lifetime/provenance and all error variants with canonical emitted model association; native pointer/error packet and Lean/audit still required.',
'data_len':'K099/K100 are the planned native all-usize Ok/error discrimination pair (check receipts for completion), never a composed claim. Full emitted Result error-carrier/clone correspondence and model/audit support remain OPEN; native evidence alone is insufficient.',
'require_distinct_accounts':'Needs SAME account-key identity/byte comparison arguments, all duplicate-position/first-error paths and runtime memcmp accepted-trust interface, with native local-record packet and Lean source-order composition.',
'require_verifier_checkpoint':'K051 is the planned exact owner/metadata/deferred-length Result diagnostic (check receipt for completion), without a matched control, never a composed claim. Full emitted clone/error carrier and Pubkey equality/accepted runtime memcmp interface association, data_len domain and complete raw audit remain OPEN.',
'require_readonly_account':'Needs exact account owner/key/flags domain, original metadata arguments and complete Result/error/frame model; can cite CLOSED key/owner/read-only helpers only at their established call domains. Needs native caller and Lean/audit work.',
'authenticate_invariant_release_registry':'Needs exact account order/owner/key/data borrow, registry decode and accepted authentication comparison interfaces, all abort/cleanup prefixes. OPEN data/snapshot/authentication children and out-of-assignment dependencies are not assumed; needs their packets plus caller native/model certificate.',
'authenticate_asq8_accounts':'Needs exact SAME account order/data, authentication result and all first-error/cleanup prefixes, with OPEN snapshot/data/registry/validate children instantiated. Needs real callee closure and caller native/model certificate.',
'validate_asq8':'Needs exact statement/ASQ8 payload decoder domain and same account provenance/first-error Result plus all outside-assignment child packets. Needs local native record oracle, one-window/loop composition where applicable and canonical model/audit.',
'stage1':'K054/K055 only empty-account rejection. Full decode/route argument preservation, observer deployed None rename pair under (ae), transaction result/error forwarding and abort/cleanup order remain OPEN. Transaction bodies are excluded from this assignment; cite only CLOSED packets. Needs caller native schedule and model joins.',
'stage1_owned':'K056/K057 only empty-account rejection. OPEN snapshot/data/metadata/authentication dependencies plus exact route, original arguments, return/error, observer and cleanup order prevent composed closure. Needs native schedule/model joins without assuming successful tx1.',
'stage2':'K058/K059 only empty-account rejection. Full decode/route, SAME checkpoint/statement/proof arguments and exact tx2 result/error/cleanup require child packets, observer None controls and canonical model association; tx2 itself excluded.',
'stage2_owned':'K060/K061 only empty-account rejection. OPEN account authentication/snapshot/validate/checkpoint dependencies and full route/error/cleanup order prevent closure; needs actual caller packet and model/audit, not transaction-body ownership.'}
remaining=[];lines=['# NFU remaining assigned/context members','',f"Admitted: {closed['new_composed_functions']} new functions / {closed['new_composed_rows']} new D rows; D 35/343 CLOSED, 308 OPEN. Driver OPEN. Budget charged {used} of 100 Kani/60 Lean-support/3 extraction. Receipt-only fragments have no closure credit.",'']
for f in J(E/'NFU_SCOPE.json')['members']:
 n=f['function']
 if n in cf:continue
 if all(by[r]['composed_status']=='CLOSED'for r in f['rows']):
  lines+=['## '+n,'','Already CLOSED in baseline; no duplicate NFU credit. Rows '+', '.join(f['rows'])+'.',''];continue
 short=n.rsplit('::',1)[1];reason=reasons.get(short,'Needs its own exact native Result/state/ordered-effects packet, complete caller domains, canonical model association and raw audit; no closure credit from children alone.')
 out={**f,'remaining_reason':reason,'requires_fresh_Lean_or_audit_budget':True,'native_requirement':('Conditional: existing restricted-error native pair may suffice after actual caller-domain/error-carrier proof; no assertion that this is Kani-only' if short=='data_len' else 'Missing native/source or external callee/edge packet described above; model/domain/induction/audit work also remains')};remaining.append(out)
 lines+=['## '+n,'','Rows '+', '.join(f['rows'])+'. '+reason,'','Real callees: '+('; '.join(c['function']+' ['+c['scope']+']'for c in f['callees'])or 'none')+'.','']
lines+=['No unused proof budget remains once NFU_RECEIPTS_CHECK.json passes. The outstanding model/domain/induction/audit obligations are recorded above rather than characterized as Kani-only blockers. No root or 100-bit per-attempt claim is established.','']
(E/'NFU_REMAINING.md').write_text('\n'.join(lines));(E/'NFU_REMAINING.json').write_text(json.dumps(dict(functions=remaining,budget_charged=used,driver_status='OPEN'),indent=1)+'\n')
commits=subprocess.check_output(['git','log','--format=%h %s','f87d767e34e..HEAD'],cwd=R,text=True).strip()
(E/'NFU_HANDOFF.md').write_text(f'''# NFU handoff

Branch `codex/cx-slice-d-check-20261104`; receipts `evidence/slice-d-check-20261104/`. **11 new composed functions / 14 D rows** via additive NFU_certify.py: D **35/343 CLOSED**, 308 OPEN; deployed driver remains OPEN. The 100-bit per-attempt target is not established.

NFU_CLOSED.json, NFU_EDGES.json, NFU_CERTIFICATES.json and NFU_LEDGER_DELTA.json are authoritative. Only their selected packets count; historical inventory packets are explicitly marked unselected. NFU_REMAINING.md/.json lists every remaining member and real callee/domain/join obligation. NFU_ERROR_EDGE_FINDING.md identifies the omitted first_decoded map_err(error) edge at frozen lib.rs:50; inventory untouched.

Budget charged: {used}. A final NFU_RECEIPTS_CHECK.json PASS means exactly 100 native scopes, 59 actual Lean/support scopes plus one conservatively charged prelaunch L047 failure, and 3 extraction scopes. Do not launch more under this job. K014/K020/K050/K052 timeouts, K078 memcmp-unwind failure and all compile/elaboration failures are excluded; replacements change the failed shape. No cap or timeout was raised. E001..003 and finish/metadata/guard fragments remain OPEN, not composed claims. See NFU_REFERENCE_CARRIER_FINDING.md and NFU_FINISH_CANDIDATE.json.

Coherent L057 imports 46 proof/support modules and headline AspisR1.RPx_Deployed.deployed. L059 raw-walks 151 roots, equal to collectAxioms with only standard axioms, and passes all 8 audit fixtures in the SAME optimized driver. L005 separately audits the initial 5 roots. #print axioms and exact target/exit/wall/RSS/swap/revision/source/dependency/tool pins are recorded per attempt; every explicit retarget theorem is checked by NFU_validate_retarget.py. The last generated Types preflight creates no new top theorem or closure claim. This is focused cached evidence, not a cold manifest replay.

Host workspace `/home/dombarker/project-offloads/codex-cx-slice-d-check-20261104`; retained private cache `/home/dombarker/project-offloads/codex-cx-slice-d-check-cache-20261104`. Cache is NEVER deleted. NFU_CACHE_IMPORTS.json.xz/.sha256 pins copied seeds; all 31 NFQ exports match NFU_NFQ_CACHE_CHECK.json. NFU_CACHE_END.json pins 102 retained export files. Own Rust targets and compiled-object scratch were removed after verified cache copies; restore those exports to NFU_objects before reusing receipt LEAN_PATH and selected Aeneas objects, including formatter adapter; do not substitute bare library objects or live sibling files.

All launched jobs have allowed:true AND admission exit0; unchanged S2W launcher; one own scope at a time; MemoryHigh6G/Max8G/Swap0/Tasks64, Lean -M7000; optimized offline native with frozen graph before EVERY run and identical lock afterward. Exact adopted KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 plus matched failing copy controls; no private copy stub, multiplication in Kani, writable static or credited Option<fn> dependence. No credited caller uses stub_verified. All scratch modifications are committed as patches/snapshots only.

Retained root carrier/ABI, compiler/library/Aeneas interpretation, source-to-ELF and P6/D188 optionA trust are reclassified, never removed. RuntimePersistence, digest realization, RuntimeReturnData and RuntimeMemcmp remain accepted trust. No privacy/two-transaction/per-attempt bound change. Repository crates/programs and inventory unchanged; no ELF rebuild trigger. Inherited ELF pins, not newly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Commits before this handoff update (no push):
```
{commits}
```
No merge, session-A/sibling worktree edits, wallet/key cleanup, refund or chain operations occurred. Continue only with a new lead budget and the member-by-member remaining file; do not reuse reduced-error extractions or partial native guards as caller closure.
''')
print(json.dumps(dict(charged=used,remaining_context_functions=len(remaining),new_rows=14)))
