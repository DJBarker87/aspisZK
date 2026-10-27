from pathlib import Path
import json,hashlib,re,subprocess,ast
E=Path(__file__).resolve().parent;errors=[]
def check(p,s):
 if not p:errors.append(s)
receipts=[]
for i in range(1,14):
 a=f'XRh_{i:03}';r=json.loads((E/a/'receipt.json').read_text());receipts.append(r)
 check(r['attempt']==a,a+' identity');check(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a+' caps');check(r['swaps']=='0',a+' swaps');check(r['exit_status'] not in [124,137],a+' resource stop')
 check(r['print_axioms'].startswith('N/A:'),a+' no Lean assertion')
 check(json.loads((E/(a+'-reservation.json')).read_text())['allowed'],a+' admission')
 for f,h in r['source_hashes'].items():check(hashlib.sha256((E/f).read_bytes()).hexdigest()==h,a+' source '+f)
 check(r['reservation_retries']==0,a+' admission retry')
for p in E.glob('XRh_*.py'):ast.parse(p.read_text(),filename=str(p))
for r in json.loads((E/'XRh_baseline.json').read_text()):check(hashlib.sha256((E.parents[1]/r['path']).read_bytes()).hexdigest()==r['sha256'],'baseline '+r['path'])
for name in ['ARX_Root','Rc10_Top']:check((E/f'XRh_{name}.BEFORE.lean.txt').read_bytes()==(E/f'XRh_{name}.AFTER.lean.txt').read_bytes(),'before/after '+name)
inv=json.loads((E/'XRh_inventory_summary_v2.json').read_text())
for case,r in inv.items():check(r['missing_count']==0,case+' call declaration closure');check(not r['has_errors'],case+' LLBC errors')
check(inv['full']['project_opaque_count']==0,'full release opacity')
for case,i in zip(['shared','distinct','context','borrow','arrow','full'],range(6,12)):
 r=json.loads((E/f'XRh_{case}_result.json').read_text());check(r['aeneas_sha256']=='1ead6274a06d957c188144701c127a90d54b851fb7dce40b1479cc305f6fad00',case+' Aeneas pin');check(not r['changed_release_files'],case+' release pin');check(r['llbc_sha256']==inv[case]['sha256'],case+' LLBC pin');check(r['aeneas_exit']==receipts[i-1]['exit_status'],case+' exit')
check(json.loads((E/'XRh_pinned_outputs_01.json').read_text())['exit']==0,'pinned pass')
check(not json.loads((E/'XRh_full_result.json').read_text())['outputs'],'full emission failed')
audit=json.loads((E/'XRh_HostAudit.json').read_text());check(not audit['changed_release_files'] and not audit['changed_new_tool_sources'],'source audit');check(audit['runner']['sha256']==audit['own_runner']['sha256'],'unchanged runner')
check(audit['pinned_input']['sha256']=='a8832dbd36b9987ec7288ab7580040a70b01feea31d647a97deb47b521bb5575','pinned LLBC unchanged')
changed=subprocess.check_output(['git','diff','--name-only','5f979998ac','HEAD'],cwd=E.parents[1],text=True).splitlines();check(all(p.startswith('evidence/extraction-eval1-20261027/') for p in changed),'committed scope')
summary=dict(errors=errors,attempts=len(receipts),passes=sum(r['exit_status']==0 for r in receipts),nonzero=[dict(attempt=r['attempt'],exit=r['exit_status']) for r in receipts if r['exit_status']!=0],wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),peak_cgroup_bytes=max(int(r['cgroup_memory_peak_bytes']) for r in receipts),swaps=0,pinned_aeneas_invocations=1,newer_aeneas_invocations=6,newer_charon_lowerings=6,lean_attempts=0,kani_runs=0,reservation_retries=0,max_requested_plus_existing_reservation_bytes=max((json.loads((E/(r['attempt']+'-reservation.json')).read_text())['bounded_reserved_bytes'] or 0)+8*2**30 for r in receipts),top_premises_removed=0)
(E/'XRh_Verification.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2));raise SystemExit(bool(errors))
