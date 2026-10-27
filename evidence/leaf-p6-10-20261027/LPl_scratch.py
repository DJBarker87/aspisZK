"""Reproduce the final owned scratch instrumentation from ordered base + patch.
Existing job scratch is never recreated. --check only checks its exact diff.
"""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-leaf-p6-10-20261027'
base='/home/dombarker/project-offloads/codex-cx-leaf-p6-8-20261027/LPh_src'
if '--check' in sys.argv:
 r=subprocess.run(['ssh',H,f'cat {B}/LPl_harness.patch'],capture_output=True,check=True)
 assert r.stdout==(E/'LPl_harness.patch').read_bytes()
 print('Current committed owned patch matches host scratch diff')
else:
 if subprocess.run(['ssh',H,f'test -e {B}/LPl_src']).returncode==0:
  raise SystemExit('Refuse existing owned scratch; use --check')
 subprocess.run(['ssh',H,f'cp -a {base} {B}/LPl_src'],check=True)
 subprocess.run(['scp','-q',str(E/'LPl_harness.patch'),H+':'+B+'/LPl_harness.patch'],check=True)
 subprocess.run(['ssh',H,f'cd {B}/LPl_src && git apply --check {B}/LPl_harness.patch && git apply {B}/LPl_harness.patch'],check=True)
