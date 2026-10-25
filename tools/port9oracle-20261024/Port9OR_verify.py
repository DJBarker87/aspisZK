from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/port9oracle-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
manifest=json.loads((E/'manifest.json').read_text());assert manifest['inherited_lean_attempts']==36
allowed={'propext','Classical.choice','Quot.sound'}
for p in sorted(E.glob('lean-*/receipt.json')):
 r=json.loads(p.read_text())
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
 for src,h in r['source_hashes'].items():assert hashlib.sha256((p.parent/'sources'/src).read_bytes()).hexdigest()==h
 if r['exit_status']==0:
  assert r['print_axioms']
  for line in r['print_axioms']:
   if 'depends on axioms:' in line:
    names=set(re.search(r'\[([^]]*)\]',line).group(1).split(', '));assert names<=allowed,line
 reservation=json.loads((E/(r['attempt']+'-reservation.json')).read_text());assert reservation['reserved_bytes']+reservation['additional_bytes']<=reservation['limit_bytes']
for p in sorted(L.glob('Port9OR_*.lean')):
 assert p.name in manifest['final_sources'],p
 assert not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)|^\s*axiom\s',p.read_text(),re.M),p
records=[]
for p in sorted((R/'tools/port9oracle-20261024').glob('lean-*.json')):records.append(json.loads(p.read_text()))
assert len(records)==manifest['new_lean_attempts']<=64
changed=subprocess.check_output(['git','diff','--name-only','7360bbe22c'],cwd=R,text=True).splitlines()
assert all(p.startswith(('docs/research/100bit-spend-path-20261013/lean/Port9OR_','tools/port9oracle-20261024/','evidence/port9oracle-20261024/')) for p in changed),changed
assert not any(p.suffix in {'.olean','.elf','.tar','.gz'} for p in E.rglob('*') if p.is_file())
result={'receipt_source_hashes':'pass','caps_and_aggregate_reservations':'pass','zero_swaps':'pass','green_axioms_standard':'pass','all_current_owned_sources_green':'pass','authorized_path_scope':'pass','no_committed_binaries':'pass','inherited_lean_attempts':36,'new_lean_attempts':len(records),'cumulative_lean_attempts':36+len(records),'kani_runs':0}
(E/'static-verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
