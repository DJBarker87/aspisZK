#!/usr/bin/env python3
"""Collect text receipts only; never copy binaries or LLBC artifacts."""
import json, subprocess, re, hashlib
from pathlib import Path
E=Path(__file__).resolve().parent.parent
R='/home/dombarker/project-offloads/codex-cx-prover-commit48-20261022'
HOST='dombarker@100.108.41.90'
def sync(remote,local,extra=()):
 local.mkdir(parents=True,exist_ok=True)
 subprocess.run(['rsync','-az',*extra,HOST+':'+remote+'/',str(local)+'/'],check=True)


sync(R,E/'pins',('--exclude=/program-one-transition-*','--exclude=/binary-group-v*','--exclude=/binary-cursor-v*','--exclude=/stored-node-v*','--include=/*-reservations.json','--include=/*-inputs.json','--include=/*-llbc.json','--include=/lean-*.json','--include=/revision.txt','--include=/frozen-elf-final-check.json','--exclude=*'))
# Batch all scoped text receipt paths in one rsync transfer. Refresh every log,
# including receipts captured before the corresponding process completed.
records=[]
pins=sorted((E/'pins').glob('lean-*.json'))
paths=[]
for pin in pins:
 rec=json.loads(pin.read_text());a=str(rec['attempt'])
 for kind,ext in [('out','log'),('time','log'),('sha','txt')]:
  paths.append(kind+'-'+a+'.'+ext)
stage=E/'lean'/'collected-text';stage.mkdir(parents=True,exist_ok=True)
subprocess.run(['rsync','-az','--files-from=-',HOST+':/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/',str(stage)+'/'],input='\n'.join(paths)+'\n',text=True,check=True)
for pin in pins:
 rec=json.loads(pin.read_text());a=str(rec['attempt'])
 dest=E/'lean'/'receipts'/a;dest.mkdir(parents=True,exist_ok=True)
 for kind,ext in [('out','log'),('time','log'),('sha','txt')]:
  name=kind+'-'+a+'.'+ext
  (dest/name).write_bytes((stage/name).read_bytes())
 log=(dest/('out-'+a+'.log')).read_text();tl=(dest/('time-'+a+'.log')).read_text()
 def field(s):
  m=re.search(re.escape(s)+r':\s*(.+)',tl);return m[1] if m else None
 rec.update(exit_status=re.findall(r'^exit=(\d+)$',log,re.M),wall=field('Elapsed (wall clock) time (h:mm:ss or m:ss)'),peak_rss_kib=field('Maximum resident set size (kbytes)'),swaps=field('Swaps'),print_axioms=re.findall(r"^'[^']+' depends on axioms: \[.*?\]|^'[^']+' does not depend on any axioms",log,re.M|re.S),errors=[l for l in log.splitlines() if 'error' in l])
 # Exact source bytes are retained alongside each attempt, including rejected attempts.
 snapshot=next((E/'lean'/'sources').glob('attempt-'+a+'-*'),None)
 if snapshot:rec['source_snapshot']=str(snapshot.relative_to(E));assert hashlib.sha256(snapshot.read_bytes()).hexdigest()==rec['source_sha256']
 rec['source_revision']=(E/'pins'/'revision.txt').read_text().strip()
 rec['exact_command']=['sh',R+'/run-joint.sh',a,rec['module'][:-5],'J','7000','8',rec['deps_fingerprint']]
 rec['source_revision_description']='Task base revision plus this exact source SHA256 and retained dependency-object fingerprint; no attribution to an unchanged checkout.'
 records.append(rec)
for p in stage.iterdir():p.unlink()
stage.rmdir()
records.sort(key=lambda r:r['attempt'])
(E/'lean'/'attempts.json').write_text(json.dumps(records,indent=2)+'\n')


sync(R+"/receipts",E/"native-receipts")
sync(R+"/input-snapshots",E/"native-snapshots")
