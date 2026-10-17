#!/usr/bin/env python3
"""Read/hash-only validation of the historical-context downgrade."""
from pathlib import Path
import hashlib,json,runpy
ROOT=Path(__file__).resolve().parents[5]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/c2-historical-context-20261017'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=E/'audit.json';assert sha(p)=='d599abdfd7ca2ebd44a9b24e111596bf13d94b47f089912b6bd4b5de1ee973e8'
 a=json.loads(p.read_text());assert a['classification']=='HISTORICAL_CONTEXT_ONLY' and a['affected_formal_results']==13
 assert a['current_accepted_semantic_model_results']==0
 assert sha(E/'historical-environment.json')==a['environment_sha256']
 assert sha(E/'c-current-frontier.json')==a['frontier_sha256']
 imports=runpy.run_path(str(Path(__file__).with_name('audit-historical-context.py')))['imports']
 for name,n in a['nodes'].items():
  src=E/n['source_snapshot'];assert sha(src)==n['source_sha256'],name
  assert imports(src.read_text())==n['direct_imports'],name
 for chain in a['paths']:
  for x,y in zip(chain,chain[1:]):assert y in a['nodes'][x]['direct_imports'],(x,y)
 for m in ['FS2.Duplex','AspisV8R19.UniformStateFirstHit']:
  assert a['frontier'][m]['matches_historical'] and not a['frontier'][m]['matches_repaired']
 assert a['frontier']['AspisFormal.CircleGroupOrder']['matches_repaired']
 print(json.dumps({'status':'PASS','classification':a['classification'],'historical_results':13,'current_semantic_model_results':0,'witness_paths':len(a['paths']),'audit_sha256':sha(p)},sort_keys=True))
if __name__=='__main__':main()
