#!/usr/bin/env python3
"""Rehash the exact retained source snapshot; optionally upload only those files."""
import argparse,hashlib,json,subprocess,tempfile
from pathlib import Path
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023'
a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');a.add_argument('--upload',action='store_true');args=a.parse_args()
x=json.loads((E/'source-inputs.json').read_text())
for r in x['files']:
 p=R/r['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'] and p.stat().st_size==r['bytes'],p
if args.upload:
 with tempfile.NamedTemporaryFile(mode='w') as f:
  f.write('\n'.join(r['path'] for r in x['files'])+'\n');f.flush()
  p=subprocess.Popen(['tar','-cf','-','-T',f.name],cwd=R,stdout=subprocess.PIPE)
  q=subprocess.run(['ssh','dombarker@100.108.41.90','tar -xf - -C /home/dombarker/project-offloads/codex-cx-s10-repin3-20261023/src'],stdin=p.stdout)
  assert q.returncode==0 and p.wait()==0
print(json.dumps(dict(files=len(x['files']),bytes=sum(r['bytes'] for r in x['files']),changed=[r['path'] for r in x['files'] if r['changed']],source_revision=x['source_revision'])))
