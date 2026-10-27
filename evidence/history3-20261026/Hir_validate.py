from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parent
repo=root.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads((root/f'Hir_{n:03}/receipt.json').read_text()) for n in range(1,101)]
assert len(receipts)==100
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['limits']==limits and r['swaps']=='0',r['attempt']
 assert '-M7000' in r['command'] and '-j1' in r['command']
 assert r['exit_status'] not in [124,137],r['attempt']
 for name,digest in r['source_hashes'].items():
  assert sha(root/r['attempt']/'sources'/name)==digest
 if r['exit_status']==0:
  for line in r['print_axioms']:
   assert 'sorryAx' not in line
   names=re.search(r'\[([^\]]*)\]',line)
   if names: assert set(names.group(1).split(', '))<={'propext','Classical.choice','Quot.sound'}
host={line.split(None,1)[1].strip():line.split()[0] for line in (root/'Hir_host-hashes.txt').read_text().splitlines()}
modules=[]
for source in sorted((repo/'lean').glob('Hir_*.lean')):
 text=source.read_text();digest=sha(source)
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+max(?:RecDepth|Heartbeats)',text,re.M),source
 accepted=[r for r in receipts if r['exit_status']==0 and r['source_hashes'].get(source.name)==digest]
 assert len(accepted)==1,(source.name,len(accepted))
 receipt=accepted[0]
 assert host[source.name]==digest,source.name
 ns=re.search(r'^namespace (\S+)',text,re.M)
 if ns:
  declared={ns.group(1)+'.'+name for name in re.findall(r'^theorem\s+(\S+)',text,re.M)}
  printed={re.search(r"'([^']+)'",line).group(1) for line in receipt['print_axioms']}
  assert declared<=printed,(source.name,declared-printed)
 for dep,info in receipt['deps_fingerprint']['selected_objects'].items():
  name=Path(info['path']).name
  if name.startswith('Hir_') and name.endswith('.olean'):
   assert host[name]==info['sha256'],(source.name,name)
 modules.append({'module':source.stem,'source_sha256':digest,'object_sha256':host[source.stem+'.olean'],'accepted':receipt['attempt'],'axioms':receipt['print_axioms']})
rust_pins=json.loads((root/'Hir_rust-source-pins.json').read_text())['source_hashes_matching_host']
for name,digest in rust_pins.items(): assert sha(repo/name)==digest,name
stage=json.loads((root/'Hir_stage0.json').read_text())
for name,pin in stage['source_pins'].items():assert sha(repo/name)==pin['sha256'],name
changed=subprocess.check_output(['git','diff','--name-only',stage['base']],cwd=repo,text=True).splitlines()
assert all(name.startswith(('lean/Hir_','evidence/history3-20261026/')) for name in changed)
for n in range(1,6):
 r=json.loads((root/f'Hir_KANI{n:03}/receipt.json').read_text())
 assert r['exit_status']==0 and r['limits']==limits and r['swaps']=='0'
 assert r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
original_forest=(repo/'programs/aspis-pool/src/pair_forest.rs').read_bytes()
original_processor=(repo/'programs/aspis-pool/src/processor.rs').read_bytes()
for n,overlays in [(1,['Hir_pool_harness.rs']),(2,['Hir_pool_harness.rs']),(3,['Hir_pool_harness.rs']),(4,['Hir_pool_harness.rs','Hir_encoded_harness.rs']),(5,['Hir_pool_harness.rs','Hir_encoded_harness.rs','Hir_read_harness.rs'])]:
 p=root/f'Hir_KANI{n:03}'/'sources'/'Hir_src/programs/aspis-pool/src'
 assert (p/'pair_forest.rs').read_bytes()==original_forest+b''.join((root/name).read_bytes() for name in overlays)
 if n>=3:assert (p/'processor.rs').read_bytes()==original_processor+(root/'Hir_close_harness.rs').read_bytes()
audit=receipts[-1];targets=json.loads((root/'Hir_audit-targets.json').read_text())['axiom_targets']
assert {re.search(r"'([^']+)'",line).group(1) for line in audit['print_axioms']}==set(targets)
result={'lean_submissions':100,'passing':sum(r['exit_status']==0 for r in receipts),'failed':[r['attempt'] for r in receipts if r['exit_status']],'kani_runs':5,'kani_harnesses':6,'lean_wall_sum_seconds':sum(r['wall_seconds'] for r in receipts),'max_peak_rss_kib':max(int(r['peak_rss_kib']) for r in receipts),'all_swap_counts_zero':True,'final_audit':{k:audit[k] for k in ['attempt','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']},'current_modules':modules,'shipped_source_pins_unchanged':True,'global_ledger_rows_removed':[],'status':'budget exhausted; target not yet established'}
(root/'Hir_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['lean_submissions','passing','kani_runs','kani_harnesses','lean_wall_sum_seconds','max_peak_rss_kib','global_ledger_rows_removed','status']}))
