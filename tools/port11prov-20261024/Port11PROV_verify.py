from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/port11prov-20261024';T=R/'tools/port11prov-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
manifest=json.loads((E/'manifest.json').read_text());cfgs=sorted(T.glob('lean-*.json'))
assert len(cfgs)==manifest['new_lean_attempts']<=60
assert manifest['cumulative_lean_attempts']==160+len(cfgs)
assert manifest['remaining_lean_attempts']==60-len(cfgs)
for cfg in cfgs:
 a=cfg.stem;r=json.loads((E/a/'receipt.json').read_text())
 assert r['swaps']=='0'
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 admission=json.loads((E/(a+'-reservation.json')).read_text())
 assert admission['reserved_bytes']+admission['additional_bytes']<55*1024**3
 assert r['peak_rss_kib'] and r['command'] and r['deps_fingerprint']['selected_objects']
 for src,h in r['source_hashes'].items():
  assert hashlib.sha256((E/a/'sources'/src).read_bytes()).hexdigest()==h
for p in L.glob('Port11PROV_*.lean'):
 h=hashlib.sha256(p.read_bytes()).hexdigest();final=manifest['final_sources'][p.name]
 assert final['sha256']==h
 r=json.loads((E/final['attempt']/'receipt.json').read_text());assert r['exit_status']==0
 for report in r['print_axioms']:
  for ax in re.search(r'\[(.*?)\]',report,re.S).group(1).split(','):
   assert ax.strip() in ['propext','Classical.choice','Quot.sound']
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',p.read_text()),p
owned=json.loads((E/'owned-theorems.json').read_text());audit=json.loads((E/'lean-025/receipt.json').read_text())
assert audit['exit_status']==0
for theorem in owned:
 assert any(report.startswith("'"+theorem+"'") for report in audit['print_axioms']),theorem
# Historical private helper audited in its own smallest compiled file.
assert any('_private.Port11PROV_WriterRoots' in s for s in json.loads((E/'lean-017/receipt.json').read_text())['print_axioms'])
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=5*1024**2, p
changed=subprocess.check_output(['git','diff','--name-only','7b887b23ac6e1fc5db1a30ff64fad11125935275'],cwd=R,text=True).splitlines()
for path in changed:
 assert path.startswith(('docs/research/100bit-spend-path-20261013/lean/Port11PROV_','evidence/port11prov-20261024/','tools/port11prov-20261024/')),path
subprocess.run(['python3',str(T/'Port11PROV_auth_gen.py'),'--check'],check=True)
summary={'status':'passed','final_module_count':len(manifest['final_sources']),'public_theorems_audited':len(owned),'private_helpers_audited':1,'counted_attempts':len(cfgs),'pre_lean_rejections':len(cfgs)-manifest['actual_lean_receipts'],'resource_failures':0,'cumulative_lean_attempts':160+len(cfgs),'remaining_lean_attempts':60-len(cfgs),'kani_runs':0,'source_scope_verified':True,'new_identity_gate':False}
(E/'verification.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
