#!/usr/bin/env python3
"""Final noncompiler path/hash/receipt seal; no donor/cache/compiler operations."""
import ast,hashlib,json,resource,subprocess,time
from pathlib import Path
T=Path(__file__).resolve().parent;R=T.parents[1];E=R/'evidence/port28rootexport-20261024'
def pin(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return dict(path=str(p),sha256=h.hexdigest(),bytes=p.stat().st_size)
def main():
 start=time.monotonic();a=json.loads((E/'Port28ROOTEXPORT_correction-audit.json').read_text());r=json.loads((E/'Port28ROOTEXPORT_lean2.receipt.json').read_text())
 assert r['exit_status']==0 and r['lean_invocations_charged']==1 and a['total_job_lean_invocations']==2
 assert pin(T/'Port28ROOTEXPORT_Raw.lean')==r['tool']
 assert pin(Path(a['output_audit_manifest']['path']))==a['output_audit_manifest']
 assert pin(Path(a['stdout']['path']))==a['stdout']
 assert a['missing_seed_names']==[] and len(a['unresolved_names'])==323
 assert a['duplicate_name_groups']==a['duplicate_byte_identical_transport_groups']==328
 for p in T.glob('*.py'):ast.parse(p.read_text())
 paths=subprocess.check_output(['git','diff','--name-only','438e20f4e4f8596b2d812f6f98a7f5b285827dc0'],text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines()
 assert all(p.startswith(('tools/port28rootexport-20261024/','evidence/port28rootexport-20261024/')) for p in paths)
 pins=[pin(R/p) for p in sorted(set(paths)) if not p.endswith('Port28ROOTEXPORT_correction-seal.json')]
 assert all(x['bytes']<=5_000_000 for x in pins)
 result=dict(status='PASS final path-limited source/evidence/hash seal; no compiler',command=['python3','-B',str(Path(__file__).resolve())],exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(0).ru_maxrss,swaps=resource.getrusage(0).ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,files=pins,output_manifest=a['output_audit_manifest'],print_axioms='N/A: no theorem',new_lean_invocations=0)
 (E/'Port28ROOTEXPORT_correction-seal.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ['status','exit_status','wall_seconds','peak_rss_bytes','swaps']}))
if __name__=='__main__':main()
