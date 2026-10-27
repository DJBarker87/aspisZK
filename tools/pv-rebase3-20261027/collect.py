"""Collect text-only task receipts; never copy artifact keys or raw proofs."""
import subprocess,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[2];H='/home/dombarker/project-offloads/codex-pv-rebase3-20261027';HOST='dombarker@100.108.41.90';E=ROOT/'evidence/pv-rebase3-20261027'
query='''import pathlib,json
h=pathlib.Path(%r)
files=[]
for p in h.rglob('*'):
 r=p.relative_to(h);s=str(r)
 if any(x in r.parts for x in ['src','native-target','sbf-target-verifier','sbf-target-pool','artifacts','diagnostics','bin','fixtures-candidate','fixtures-research']):continue
 if p.is_file() and p.name in ['receipt.json','time.log','stdout.log','stderr.log','reservation.json','command.json','comparison.json','binary-pins.json','fixture-comparison.json','meta.json','route-symbols.json','route-disassembly.txt','symbols.txt','relocations.txt','key-retention.json','source-verification.json'] or (p.is_file() and p.name.endswith('-launcher.log')):
  files.append(s)
print(json.dumps(files))
'''%H
import json
files=json.loads(subprocess.check_output(['ssh',HOST,'python3 -c '+__import__('shlex').quote(query)],text=True))
for p in files:
 dst=E/p;dst.parent.mkdir(parents=True,exist_ok=True)
 subprocess.run(['scp','-q',HOST+':'+H+'/'+p,str(dst)],check=True)
print('Collected',len(files),'text receipts')
