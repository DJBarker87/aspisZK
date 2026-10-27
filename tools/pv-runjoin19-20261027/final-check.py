from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin19-20261027'
rows=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
assert len(rows)==100 and all(r['exit'] is not None for r in rows)
latest={}
for r in rows:
 if r['accepted']:latest[r['target']]=r
status=[]
for m,r in sorted(latest.items()):
 p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean');actual=hashlib.sha256(p.read_bytes()).hexdigest()
 assert actual==r['source_sha256'],m
 status.append(dict(module=m,path=str(p.relative_to(R)),attempt=r['attempt'],sha256=actual,byte_equal=True))
 for line in r['axioms']:
  m=re.search(r'axioms: \[([\s\S]*?)\]',line)
  if m:assert {s.strip() for s in m[1].split(',')} <= {'propext','Classical.choice','Quot.sound'}
for p in (R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RunJoin_*19.lean'):
 if p.is_file() and subprocess.run(['git','cat-file','-e','fd42d798ff:'+str(p.relative_to(R))],cwd=R,capture_output=True).returncode != 0:
  assert 'R1Z/'+p.stem in latest,('unaccepted source',str(p))
diff=subprocess.check_output(['git','diff','--name-only','fd42d798ff','--','crates','programs'],cwd=R,text=True);assert not diff
for s in status:
 text=(R/s['path']).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b',text)
 assert not re.search(r'^\s*axiom\b',text,re.M)
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',text)
(E/'proof-status.json').write_text(json.dumps(dict(accepted_modules=status,unaccepted_proof_sources=[],shipped_source_diff=[],trust_definition_changes=False,simulator_observer_changes=False),indent=2)+'\n')
print(len(status),'accepted modules match exact compile snapshots; no unaccepted Lean sources; shipped diff empty')
