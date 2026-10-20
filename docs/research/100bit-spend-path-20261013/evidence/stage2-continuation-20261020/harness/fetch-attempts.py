#!/usr/bin/env python3
"""Fetch completed receipts and hashes; retain large raw debug traces on the host."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parents[1];H='/home/dombarker/project-offloads/codex-cx-stage2b-20261020';remote='dombarker@100.108.41.90'
p=E/'harness/pin-attempts.py';s=p.read_text()
for a in sys.argv[1:]:
 if repr(a) not in s:s=s.replace("'reader-queries-47']","'reader-queries-47',"+repr(a)+']') if "'reader-queries-47']" in s else s.replace(']:\n d=H/',','+repr(a)+']:\n d=H/')
p.write_text(s)
subprocess.run(['scp',str(p),remote+':'+H+'/harness-continuation/pin-attempts.py'],check=True)
subprocess.run(['ssh',remote,'python3 '+H+'/harness-continuation/pin-attempts.py'],check=True)
for a in sys.argv[1:]:
 d=E/'attempts'/a;assert d.exists()
 subprocess.run(['scp','-r',remote+':'+H+'/continuation-pins/'+a+'/.',str(d)],check=True)
 for phase in ['charon','aeneas']:
  subprocess.run(['scp','-r',remote+':'+H+'/receipts/extract-'+a+'-'+phase,str(d)],check=True)
subprocess.run([sys.executable,str(E/'harness/compact-traces.py')],check=True)
subprocess.run([sys.executable,str(E/'harness/summarize-attempts.py')],check=True)
