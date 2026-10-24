#!/usr/bin/env python3
"""Noncompiler pin and syntax/API review evidence; reuses prior source preflight."""
import ast,hashlib,json,resource,sys,time
from pathlib import Path
T=Path(__file__).resolve().parent;E=T.parents[1]/'evidence/port28rootexport-20261024'
def pin(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return dict(path=str(p),sha256=h.hexdigest(),bytes=p.stat().st_size)
def main():
 start=time.monotonic();old=json.loads((E/'Port28ROOTEXPORT_diagnostic-preflight.json').read_text())
 manifest=Path(old['full_manifest']['path']);assert pin(manifest)==old['full_manifest']
 full=json.loads(manifest.read_text())
 for x in full['object_parts']:
  p=Path(x['retained_path']);assert not p.is_symlink() and p.stat().st_nlink==1
  y=pin(p);assert y['sha256']==x['sha256'] and y['bytes']==x['bytes']
 for x in full['core_parts']+full['runtime']+full['inputs']:
  assert pin(Path(x['path']))==x
 for p in T.glob('*.py'):ast.parse(p.read_text())
 hist=pin(T/'Port28ROOTEXPORT_Raw-failed-attempt1.lean.txt');assert hist['sha256']==old['tool']['sha256']
 src=(T/'Port28ROOTEXPORT_Raw.lean').read_text()
 assert src.count('#eval ')==1 and '#eval!' not in src and src.startswith('import Lean\n')
 assert src.count('(0 : Nat)')==2 and '{ data with\n' in src
 assert all(s not in src for s in ['maxRecDepth','maxHeartbeats','addDeclCore','importModules','setEnv','unsafeCast'])
 out=dict(old,status='PASS correction static/pin check; prior source-only preflight reused',tool=pin(T/'Port28ROOTEXPORT_Raw.lean'),historical_failed_source=hist,input_directory=old['retained'],
  reused_input_manifest_contains_historical_tool_pin=True,source_revision_basis='438e20f4e4f8596b2d812f6f98a7f5b285827dc0',
  source_only_preflight='REUSED, not rerun',lean_invocations=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(0).ru_maxrss,swaps=resource.getrusage(0).ru_nswap,
  python_runtime=pin(Path(sys.executable).resolve()))
 (E/'Port28ROOTEXPORT_correction-preflight.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:out[k] for k in ['status','wall_seconds','peak_rss_bytes','tool','historical_failed_source']}))
if __name__=='__main__':main()
