#!/usr/bin/env python3
"""Read/hash-only restriction of C's current closure to Aeneas imports."""
import argparse,hashlib,json
from pathlib import Path
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 snapshot=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-typedfull-current-20261017/external-inputs.json')
 env=Path('/home/dombarker/project-offloads/aspis-c2-owned-lean-20261017/primitive-environment.json')
 v=json.loads(snapshot.read_text());e=json.loads(env.read_text());roots=[Path(p) for p in e['LEAN_PATH'].split(':')]
 seen=set();todo=['Aeneas'];nodes={}
 while todo:
  m=todo.pop()
  if m in seen:continue
  seen.add(m);n=v['modules'][m];todo+=n['imports']
  assert not m.startswith(('FS2.','AspisFormal.','AspisV8R19.','RawCut','R1Literal')),m
  rel=m.replace('.','/')+'.olean';obj=next(p for r in roots if (p:=r/rel).is_file())
  assert sha(obj)==n['objects']['.olean']['sha256'],(m,obj)
  assert sha(Path(n['source']))==n['source_sha256'],m
  if 'build_receipt' in n:assert sha(Path(n['build_receipt']['path']))==n['build_receipt']['sha256'],m
  nodes[m]={**n,'resolved_object_path':str(obj),'resolved_object_sha256':sha(obj)}
 report={'scope':'Exact Aeneas-only transitive closure from C current external snapshot, source/object hashes checked against actual paths selected by primitive environment; no semantic model module imported.',
  'external_snapshot_path':str(snapshot),'external_snapshot_sha256':sha(snapshot),'environment_sha256':sha(env),
  'roots':[str(p) for p in roots],'entry':'Aeneas','module_count':len(nodes),'modules':nodes,
  'runtime_files':v['runtime_files'],'runtime_root':v['runtime_root'],'packages':v['packages'],
  'excluded_semantic_models':['R1LiteralSemanticPrefix','RawCutConstructedWords','FS2.Duplex','AspisV8R19.UniformStateFirstHit','AspisFormal.CircleGroupOrder']}
 a.out.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':'PASS','module_count':len(nodes),'sha256':sha(a.out)}))
if __name__=='__main__':main()
