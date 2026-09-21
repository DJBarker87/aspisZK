#!/usr/bin/env python3
"""Compile and run independent models; no network, repo writes or SBF claims."""
import argparse,json,shutil,subprocess,tempfile
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--compiler',default='g++');a=p.parse_args()
root=Path(__file__).resolve().parent;cc=shutil.which(a.compiler)
if not cc:raise SystemExit('C++ compiler unavailable')
results={}
with tempfile.TemporaryDirectory(prefix='aspis-r19-') as td:
 for name in ['checks','channel_fold']:
  exe=Path(td)/name
  subprocess.run([cc,'-std=c++17','-O2','-DEXTENSION',str(root/'tests'/f'{name}.cpp'),'-o',str(exe)],check=True,timeout=45)
  result=json.loads(subprocess.check_output([str(exe)],text=True,timeout=45))
  if not result.get('all_passed'):raise SystemExit(f'FAIL {name}')
  results[name]=result
print(json.dumps(results,indent=2))
