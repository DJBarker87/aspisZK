from pathlib import Path
import subprocess,json,hashlib,time,re,datetime
B=Path('/home/dombarker/project-offloads');T=B/'aspis-fs-generic-20261006/evidence';H=B/'r1-privacy-build-integration-20261019';J=B/'aspis-joint-20261019'
rs=[json.loads(l) for l in (T/'EJR_attempts.jsonl').read_text().splitlines()];assert len(rs)<800
attempt=30000+len(rs);label='EJR-'+str(attempt);src=J/'sources/R1Z/EJR_Verification.lean';obj=J/'objects/R1Z/EJR_Verification.olean';env=json.loads((H/'env/J.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=[J/'objects']+[Path(p) for p in env['LEAN_PATH'].split(':')];dep=next(p/'R1Z/CertSound.olean' for p in paths if (p/'R1Z/CertSound.olean').is_file());ds=[dict(module='R1Z/CertSound',path=str(dep),sha256=sha(dep))];fp=hashlib.sha256(json.dumps(ds,sort_keys=True).encode()).hexdigest()
for retry in range(11):
 receipt=T/(label+f'-reservation-{retry}.json');log=T/(label+f'-reservation-{retry}.log')
 with log.open('w') as f:rc=subprocess.run(['python3',str(B/'codex-cx-s2x-20261023/S2X_reservation.py'),str(receipt)],stdout=f,stderr=subprocess.STDOUT).returncode
 if not receipt.exists():
  if retry==0:time.sleep(30);continue
  raise RuntimeError('missing reservation JSON')
 r=json.loads(receipt.read_text())
 if r.get('allowed'):break
 if rc not in (0,78):raise RuntimeError('reservation failure')
 if retry==10:raise RuntimeError('reservation exhausted')
 time.sleep(180)
cmd=['sh',str(H/'tools/run-joint.sh'),str(attempt),'R1Z/EJR_Verification','J','7000','8',fp];start=time.monotonic()
with (T/(label+'-launcher.log')).open('w') as f:outer=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT).returncode
out=(T/f'out-{attempt}.log').read_text();tim=(T/f'time-{attempt}.log').read_text();ec=int(re.search(r'Exit status:\s*(\d+)',tim)[1]);axioms=[l for l in out.splitlines() if 'axioms' in l];assert 'successor_nonzero' in out
r=dict(key='joint:R1Z/EJR_Verification',attempt=attempt,module='R1Z/EJR_Verification',workspace='joint',source_sha256=sha(src),source_revision=(T/'EJR_revision.txt').read_text().strip(),source_blob_revision=(T/'EJR_revision.txt').read_text().strip(),source_repository_path='evidence/envj-rebuild-20261026/EJR_Verification.lean',command=cmd,deps=ds,deps_fingerprint=fp,exit=ec,outer_exit=outer,wall_seconds=time.monotonic()-start,time_log=tim,peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',tim)[1]),swaps=int(re.search(r'Swaps:\s*(\d+)',tim)[1]),axioms=axioms,errors=[l for l in out.splitlines() if 'error:' in l],admission={'receipt':str(receipt),'retries':retry},caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000),object_sha256=sha(obj) if ec==0 else None,object_bytes=obj.stat().st_size if ec==0 else None)
with (T/'EJR_attempts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
(T/'EJR_smoke.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));assert ec==0 and not any('sorryAx' in l for l in axioms)
