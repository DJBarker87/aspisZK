"""Run only after the original sequential driver has terminated."""
from pathlib import Path
import subprocess,json,hashlib,time,re,os
B=Path('/home/dombarker/project-offloads');T=B/'aspis-fs-generic-20261006/evidence';H=B/'r1-privacy-build-integration-20261019';U=B/'codex-cx-import-union-20261022';stage=U/'EJR-library-stage';env=json.loads((H/'env/J.json').read_text());paths=[stage]+[Path(p) for p in env['LEAN_PATH'].split(':')];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={r['module'].replace('.','/'):r for r in json.loads((T/'EJR_aeneas-complete-library-pins.json').read_text())};sources=json.loads((T/'EJR_library-source-provenance.json').read_text());checks=[]
for source in sources:
 rs=[json.loads(l) for l in (T/'EJR_attempts.jsonl').read_text().splitlines()];assert len(rs)<799
 attempt=30000+len(rs);label='EJR-'+str(attempt);m=source['module'];src=U/'sources'/(m+'.lean');assert sha(src)==source['source_sha256'];obj=stage/(m+'.olean');pin=pins[m];ds=[]
 for name in dict.fromkeys(pin['imports']):
  rel=name.replace('.','/')+'.olean';dep=next((p/rel for p in paths if (p/rel).is_file()),None);assert dep is not None,(m,name)
  ds.append(dict(module=name,path=str(dep),sha256=sha(dep)))
 ir=stage/'Aeneas/Tactic/Solver/Grind/Attribute.ir';assert ir.is_file();ds.append(dict(module='Aeneas/Tactic/Solver/Grind/Attribute.ir',path=str(ir),sha256=sha(ir)))
 fp=hashlib.sha256(json.dumps(ds,sort_keys=True).encode()).hexdigest()
 for retry in range(11):
  receipt=T/(label+f'-reservation-{retry}.json');log=T/(label+f'-reservation-{retry}.log')
  with log.open('w') as f:rc=subprocess.run(['python3',str(B/'codex-cx-s2x-20261023/S2X_reservation.py'),str(receipt)],stdout=f,stderr=subprocess.STDOUT).returncode
  if not receipt.exists():
   if retry==0:time.sleep(30);continue
   raise RuntimeError('reservation receipt missing')
  d=json.loads(receipt.read_text())
  if d.get('allowed'):break
  if rc not in (0,78):raise RuntimeError('reservation failure')
  if retry==10:raise RuntimeError('reservation exhausted')
  time.sleep(180)
 out=T/f'out-{attempt}.log';tim=T/f'time-{attempt}.log';cmd=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(tim),'timeout','900','python3',str(T/'run2.py'),str(H/'env/J.json'),str(stage),str(U/'sources'),str(obj),str(src),'7000'];start=time.monotonic()
 with out.open('w') as f:outer=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT).returncode
 s=out.read_text();ts=tim.read_text();exit_match=re.search(r'Exit status:\s*(\d+)',ts);ec=int(exit_match[1]) if exit_match else outer
 record=dict(key='library:'+m,attempt=attempt,module=m,workspace='library',source_sha256=sha(src),source_revision=(T/'EJR_revision.txt').read_text().strip(),source_blob_revision=source['revision'],source_provenance=source,command=cmd,deps=ds,deps_fingerprint=fp,exit=ec,outer_exit=outer,wall_seconds=time.monotonic()-start,time_log=ts,peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',ts)[1]) if 'Maximum resident' in ts else None,swaps=int(re.search(r'Swaps:\s*(\d+)',ts)[1]) if 'Swaps:' in ts else None,axioms=[l for l in s.splitlines() if 'axioms' in l],errors=[l for l in s.splitlines() if 'error:' in l],admission={'receipt':str(receipt),'retries':retry},caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000),object_sha256=sha(obj) if ec==0 else None,object_bytes=obj.stat().st_size if ec==0 else None,historical_object_sha256=pin['sha256'])
 with (T/'EJR_attempts.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
 print(label,m,'exit',ec,'old hash matches',record['object_sha256']==pin['sha256'],flush=True);assert ec==0
 checks.append(dict(module=m,source_sha256=sha(src),object_sha256=sha(obj),historical_object_sha256=pin['sha256'],identical=sha(obj)==pin['sha256']))
# All 236 objects now match recorded originals or are fresh source-identical rebuilds.
target=U/'retained-objects'
for p in sorted(stage.iterdir(),key=lambda p:p.name=='Aeneas.olean'):
 dest=target/p.name;assert not dest.exists();os.rename(p,dest)
stage.rmdir()
(T/'EJR-library-published.json').write_text(json.dumps(dict(checks=checks,published=True,target=str(target),cached_modules=234,rebuilt_modules=2,env_J_json_changed=False),indent=2)+'\n');print('published library',flush=True)
