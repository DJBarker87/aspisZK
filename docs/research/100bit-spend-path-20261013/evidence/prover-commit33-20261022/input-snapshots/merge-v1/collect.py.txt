#!/usr/bin/env python3
"""Collect text receipts only; never copy binaries or LLBC artifacts."""
import json, subprocess, re, hashlib
from pathlib import Path
E=Path(__file__).resolve().parent.parent
R='/home/dombarker/project-offloads/codex-cx-prover-commit33-20261022'
HOST='dombarker@100.108.41.90'
def sync(remote,local,extra=()):
 local.mkdir(parents=True,exist_ok=True)
 subprocess.run(['rsync','-az',*extra,HOST+':'+remote+'/',str(local)+'/'],check=True)
sync(R+'/receipts',E/'receipts')
sync(R,E/'pins',('--include=/*-inputs.json','--include=/*-llbc.json','--include=/lean-*.json','--include=/revision.txt','--include=/frozen-elf-final-check.json','--exclude=*'))
records=[]
for pin in sorted((E/'pins').glob('lean-*.json')):
 rec=json.loads(pin.read_text());a=str(rec['attempt'])
 dest=E/'lean'/'receipts'/a;dest.mkdir(parents=True,exist_ok=True)
 for kind,ext in [('out','log'),('time','log'),('sha','txt')]:
  subprocess.run(['scp','-q',HOST+':/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/'+kind+'-'+a+'.'+ext,str(dest)],check=True)
 log=(dest/('out-'+a+'.log')).read_text();tl=(dest/('time-'+a+'.log')).read_text()
 def field(s):
  m=re.search(re.escape(s)+r':\s*(.+)',tl);return m[1] if m else None
 rec.update(exit_status=re.findall(r'^exit=(\d+)$',log,re.M),wall=field('Elapsed (wall clock) time (h:mm:ss or m:ss)'),peak_rss_kib=field('Maximum resident set size (kbytes)'),swaps=field('Swaps'),print_axioms=re.findall(r'^.*depends on axioms:.*$',log,re.M),errors=[l for l in log.splitlines() if 'error' in l])
 # Exact source bytes are retained alongside each attempt, including rejected attempts.
 snapshot=next((E/'lean'/'sources').glob('attempt-'+a+'-*'),None)
 if snapshot:rec['source_snapshot']=str(snapshot.relative_to(E));assert hashlib.sha256(snapshot.read_bytes()).hexdigest()==rec['source_sha256']
 rec['source_revision']=(E/'pins'/'revision.txt').read_text().strip()
 records.append(rec)
(E/'lean'/'attempts.json').write_text(json.dumps(records,indent=2)+'\n')
