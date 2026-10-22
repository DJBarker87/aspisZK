#!/usr/bin/env python3
"""Collect text receipts only; never copy binaries or LLBC artifacts."""
import json, subprocess, re, hashlib
from pathlib import Path
E=Path(__file__).resolve().parent.parent
R='/home/dombarker/project-offloads/codex-cx-prover-commit39-20261022'
HOST='dombarker@100.108.41.90'
def sync(remote,local,extra=()):
 local.mkdir(parents=True,exist_ok=True)
 subprocess.run(['rsync','-az',*extra,HOST+':'+remote+'/',str(local)+'/'],check=True)


sync(R,E/'pins',('--include=/*-inputs.json','--include=/*-llbc.json','--include=/lean-*.json','--include=/revision.txt','--include=/frozen-elf-final-check.json','--exclude=*'))
records=[]
for pin in sorted((E/'pins').glob('lean-*.json')):
 rec=json.loads(pin.read_text());a=str(rec['attempt'])
 dest=E/'lean'/'receipts'/a;dest.mkdir(parents=True,exist_ok=True)
 if a in ('9107','9108'):
  rec.update(exit_status=[],launcher_exit_status=67,compiler_launched=False,wall=None,peak_rss_kib=None,swaps=None,print_axioms=[],errors=['Launcher refused unchanged source plus dependency fingerprint; no compiler ran.'],source_revision=(E/'pins'/'revision.txt').read_text().strip())
  rec['source_snapshot']=str(next((E/'lean'/'sources').glob('attempt-'+a+'-*')).relative_to(E))
  records.append(rec)
  continue
 for kind,ext in [('out','log'),('time','log'),('sha','txt')]:
  subprocess.run(['scp','-q',HOST+':/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/'+kind+'-'+a+'.'+ext,str(dest)],check=True)
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
# An attempted dependent install stopped before launch because its prerequisite
# object had not yet compiled. Preserve that invocation without inventing metrics.
for snapshot in sorted((E/'lean'/'sources').glob('attempt-*.lean.txt')):
 a=int(snapshot.name.split('-')[1])
 if any(rec['attempt']==a for rec in records):continue
 assert a==9164, ('unaccounted invocation',a)
 records.append(dict(attempt=a,module='R1Z/ProverCommitPreselectedNonce39.lean',
  source_sha256=hashlib.sha256(snapshot.read_bytes()).hexdigest(),
  source_snapshot=str(snapshot.relative_to(E)),
  source_revision=(E/'pins'/'revision.txt').read_text().strip(),
  compiler_launched=False,exit_status=None,orchestrator_exit_status=1,
  wall=None,peak_rss_kib=None,swaps=None,print_axioms=[],deps_fingerprint=None,
  errors=['Prerequisite object R1Z.ProverCommitReservationMemo39 absent; dependency preflight stopped before launcher. No compiler ran and no host receipt exists.']))
records.sort(key=lambda r:r['attempt'])
(E/'lean'/'attempts.json').write_text(json.dumps(records,indent=2)+'\n')
