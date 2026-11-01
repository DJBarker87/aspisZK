from pathlib import Path
import json,lzma,hashlib,re,collections
E=Path(__file__).resolve().parent
p=E/'CREDITS.json';rows=json.loads(p.read_text() if p.exists() else lzma.decompress(p.with_suffix('.json.xz').read_bytes()))
pos=json.loads((E/'host/K79200/receipt.json').read_text());neg=json.loads((E/'host/K79201/receipt.json').read_text());pl=(E/'host/K79200/output.log').read_text();nl=(E/'host/K79201/output.log').read_text()
assert pos['exit_status']==0 and '0 of 352 failed' in pl and 'VERIFICATION:- SUCCESSFUL' in pl
assert neg['exit_status']==1 and '1 of 352 failed' in nl and 'Failed Checks: assertion failed: len != r.len()' in nl
for ident in ['K79200','K79201']:
 r=json.loads((E/f'host/{ident}/receipt.json').read_text());b=json.loads((E/f'host/{ident}/barrier.json').read_text());a=json.loads((E/f'host/{ident}/admission.json').read_text());assert a['allowed']and b['allowed'];assert b['own_limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swap']==0 and r['print_axioms']=='N/A: Kani; 0 Lean'
a=json.loads((E/'host/K79200/source-sha256.json').read_text());b=json.loads((E/'host/K79201/source-sha256.json').read_text());assert a==b
start0=json.loads((E/'host/K79200/STARTED.json').read_text())['epoch'];start1=json.loads((E/'host/K79201/STARTED.json').read_text())['epoch'];assert start1-start0>=180
pair={'property':'path_checks::pathbuf_borrows','ledger_rows':['V177','V180'],'positive':pos,'control':neg,'matched_control_assertion':'len != r.len() at lib.rs:74','positive_failed_checks':0,'control_failed_checks':1,'source_hashes_equal':True,'launch_gap_seconds':start1-start0,'classifier_scope':'No writable static, stub, oracle, custom macro, include or external module in the complete standalone root','kani_result':'PASS / matched control FAIL','deployed_transfer':'WITHHELD under k-double-prime / k-triple-prime: eight differing code-symbol entries and fifteen unresolved ordinary/source mappings; see STD-PARITY.json','k2':'No function-pointer value, Option<fn>, pointer comparison or callback observation in this property; other pointer-form quarantine unchanged','native_property_counterexample':False,'budget':{'property_reruns':1,'matched_controls':1,'kani_invocations':2,'Lean':0,'allowance_exhausted':False}}
(E/'CONTROLLED-PAIR.json').write_text(json.dumps(pair,indent=2)+'\n')
for x in rows:
 if x['receipt']=='evidence/pv-cblib-20261027/kani-pathbuf-borrows-r01/collected-receipt.json':
  x['rerun']='K79200 PASS; matched K79201 FAIL at len != r.len(); local state, no stubs';x['matched_control']='host/K79201/receipt.json';x['fresh_pair']='CONTROLLED-PAIR.json';x['reason']='NOT-EXPOSED on the checked original selected input closure. Fresh controlled K-3 check passes; deployed std transfer remains WITHHELD. No new deployed-row restoration.'
for x in rows:
 # Make every no-run disposition explicit; an OPEN packet cannot be restored by a substitute property.
 if x['classification']=='OPEN':
  reasons=[]
  if x['missing_sources']:reasons.append('receipt-pinned source missing: '+str(len(x['missing_sources'])))
  if x['macro_sources']:reasons.append('unexpanded include/macro/attribute source: '+str(len(x['macro_sources'])))
  if not x['matched_sources']:reasons.append('no complete pinned selected Rust input')
  x['rerun_stop']='; '.join(reasons)+'. Remains SUSPENDED; a same-name replacement or global-log-to-local mock is not an admissible rerun.'
raw=(json.dumps(rows,indent=2)+'\n').encode();(E/'CREDITS.json.xz').write_bytes(lzma.compress(raw,preset=1));(E/'CREDITS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
if p.exists():p.unlink()
s=json.loads((E/'SUMMARY.json').read_text());s.update(new_kani_runs=2,property_reruns=1,matched_controls=1,used_IDs=['K79200','K79201'],budget_exhausted=False,remaining_rerun_work=True,std_transfer='WITHHELD',new_restored_deployed_credits=0);(E/'SUMMARY.json').write_text(json.dumps(s,indent=2)+'\n')
p=E/'K3-CREDITS.md';t=p.read_text();line=next(v for v in t.splitlines()if '`path_checks::pathbuf_borrows`'in v and 'kani-pathbuf-borrows-r01' in v);t=t.replace(line,line.replace('not re-run; unresolved closure or inherited non-credited support','K79200 PASS / K79201 matched assertion FAIL; deployed std transfer WITHHELD'))
t=t.split('\n## Controlled re-run and limits')[0]
t+="""
## Controlled re-run and limits

`path_checks::pathbuf_borrows` (shared V177/V180 gate): [K79200](host/K79200/receipt.json) PASS, exit0, wall5.786s, GNU-time peak175224KiB, swap0, source revision e46066e541f2727d757991e57208c7541dde0cd9. [K79201](host/K79201/receipt.json) matched control FAIL, exit1, wall7.060s including read-only positive-symbol inspection, peak175156KiB, swap0, revision8325d9bd00d99ac51ebb5500058e56d2c20027a5. It fails exactly `len != r.len()` at lib.rs:74, with one failed check. The same source hashes, name, bounds, no-stub configuration and profile are retained; only the negative-control feature changes the first expected equality to inequality. The scratch Cargo package name differs from the historical package; no harness/module/function was renamed and no name was varied to change a verdict. Existing K-2 pointer-route quarantine is unchanged. Exact commands/features/caps/tool hashes and N/A axioms are in the receipts and CONTROLLED-PAIR.json.

Both launches have fresh outer allowed:true/exit0 admissions and inner allowed:true cap checks. Own launches are 1107.47 seconds apart (exact value in CONTROLLED-PAIR.json); every refusal waited at least180s before the next effective admission. One early positive read-only admission probe was explicitly discarded and launched nothing; a later early control check was rejected by the time guard. ADMISSION-NOTE.json and the retained host/queue receipts record these process details. The expired quiet-window marker was not changed.

STD-REACHED.json records311 code symbols, including248 library-location entries (26 Kani model entries and222 core/alloc/std entries). The official pinned old rust-src component was read/hash-checked without installation, alongside the installed1.94.1 sources:39 file pairs. STD-PARITY.json finds197 identical body-token entries,8 differing entries,15 unresolved source mappings and2 intrinsic declarations. Intrinsics remain V370/D381/D386; unresolved ordinary/macro mappings are not relabelled as compiler proof. Differing bodies include layout_array, Global::{alloc_impl,grow_impl,deallocate}, Vec::as_slice and check_language_ub. No full per-item structural closure is claimed, so deployed transfer is WITHHELD under (k'')/(k'''). This is a successful controlled K-3 check, not a new deployed restoration.

There was no failing positive rerun and no application counterexample to report. The failing control is intentionally false. The three WITHDRAWN entries are the already-excluded historical allocator diagnostics, not new counterexamples. No ledger, endpoint, simulator, observer, trust field, production Rust, ELF or key was changed; Lean0. Endpoint premises removed/added/weakened:0/0/0. T and all original runtime/compiler/deployment/side-channel boundaries remain.

## Remaining work / stop disposition

The audit and status recommendations cover all407 rows and305 PASS observations. **The requested rerun campaign is not exhausted or complete:** only one property/control pair ran.209 OPEN packets remain suspended, with per-credit missing-input and macro names in CREDITS.json.xz; no RESTORED deployed credit is claimed. Their original source/stub/macro closure must be recovered before a faithful local-record rerun can be selected. For native-step global-log instrumentation, first check the local-context/native-step association; do not turn the observation property into a mock assertion. Highest remaining current P6 row: V185/op34_exact_word. B3 local releases retain their separate std arguments, but their broader unresolved input/expansion packets are not cleared by that alone. The earlier formal/structural/extraction row laws are preserved independently; no passing source-only scan is promoted to full privacy.

The unused Kani allowance is unspent, not reported as exhaustion. Next valid deliverable is the recovered selected closure (starting V185, then b3p6's local body packets), followed by the exact no-static property and matched failing control in fresh admitted scopes. Global-log-dependent properties remain SUSPENDED until their native-step association is checked. No source was narrowed or assertion weakened to manufacture restoration.
"""
t=t.replace("1107.47 seconds",format(pair["launch_gap_seconds"],".3f")+" seconds")
p.write_text(t)
print('Controlled positive and matched negative verified; no deployed transfer claimed')
