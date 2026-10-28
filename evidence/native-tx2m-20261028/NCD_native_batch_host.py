"""Own serial native queue, preserving per-run graph/lock/source/admission gates."""
from pathlib import Path
import json,subprocess,time,sys,hashlib,tomllib,lzma
B=Path(__file__).resolve().parent;tag=sys.argv[1];P=json.loads((B/('NCD_native_'+tag+'_plan.json')).read_text());S=Path(P['scratch']);report=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lock_hash='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
for row in P['rows']:
 a=row['cfg']['attempt'];assert not (B/a/'receipt.json').exists(),'no duplicate attempt'
 for retry in range(11):
  dest=B/(a+'-reservation.json')
  with (B/(a+f'-barrier-{retry}.log')).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(dest)],stdout=f,stderr=subprocess.STDOUT)
  try:ad=json.loads(dest.read_text())
  except (FileNotFoundError,json.JSONDecodeError):
   if retry==0:time.sleep(30);continue
   raise SystemExit('STOP missing admission JSON')
  if r.returncode==0 and ad.get('allowed') is True:break
  if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
  raise SystemExit('STOP admission failure')
 else:raise SystemExit('STOP admission exhausted')
 assert sha(S/'Cargo.lock')==lock_hash,'STOP frozen lock mismatch'
 assert all(sha(S/n)==h for n,h in P['source_manifest'].items()),'STOP scratch source drift'
 for n in ['crates/aspis-core/src/NBS_copy.rs','crates/aspis-r1-cost-probe/src/NBS_copy.rs']:assert sha(S/n)=='c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9'
 r=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--locked','--offline','--format-version','1'],cwd=S,env={**__import__('os').environ,'CARGO_NET_OFFLINE':'true'},capture_output=True,text=True)
 (B/(a+'-graph.stderr')).write_text(r.stderr);assert r.returncode==0,r.stderr
 m=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'));frozen=tomllib.loads((S/'Cargo.lock').read_text());key=lambda p:(p['name'],p['version'],p.get('source'))
 f={key(p):p for p in frozen['package']};actual={key(p):p for p in m['packages']};nodes={p['id']:p for p in m['resolve']['nodes']};pkgs={p['id']:p for p in m['packages']};added=sorted(set(actual)-set(f),key=str);errors=[]
 for p in m['packages']:
  for dep in nodes[p['id']]['dependencies']:
   q=pkgs[dep]
   if not any((bits:=label.split(' '))[0]==q['name'] and (len(bits)>1 or sum(k[0]==q['name'] for k in f)==1) and (len(bits)<2 or bits[1]==q['version']) and (len(bits)<3 or bits[2].strip('()')==q.get('source')) for label in f[key(p)].get('dependencies',[])):errors.append([key(p),key(q)])
 graph=dict(resolved_packages=len(actual),new_package_tuples=added,edge_errors=errors,graph_matches_frozen=not added and not errors,graph_sha256=hashlib.sha256(json.dumps(m,sort_keys=True).encode()).hexdigest(),lock_sha256=lock_hash)
 (B/(a+'-graph-check.json')).write_text(json.dumps(graph,indent=2)+'\n');assert graph['graph_matches_frozen']
 (B/(a+'-graph-full.json.xz')).write_bytes(lzma.compress(r.stdout.encode()));(B/(a+'-graph-full.sha256')).write_text(hashlib.sha256(r.stdout.encode()).hexdigest()+'\n')
 cfg=row['cfg'];cfg['reservation_retries']=retry;cfg['deps_fingerprint']['graph']=graph
 (B/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n');(B/(a+'-lock-before.log')).write_text(lock_hash+'\n')
 cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','S2W_run_host.py',a+'.json']
 with (B/(a+'-launcher.log')).open('wb') as log:r=subprocess.run(cmd,cwd=B,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT)
 after=sha(S/'Cargo.lock');(B/(a+'-lock-after.log')).write_text(after+'\n');assert after==lock_hash,'STOP post-run lock drift'
 p=B/a/'receipt.json';assert p.exists(),'STOP missing native receipt '+a
 rc=json.loads(p.read_text());text=(B/a/'stdout.log').read_text();report.append(dict(attempt=a,harness=cfg['command'][cfg['command'].index('--harness')+1],exit=rc['exit_status']))
 accepted=rc['exit_status']==0
 if row.get('expected_negative'):accepted=rc['exit_status']!=0 and 'Failed Checks: assertion failed: b[15] == 0' in text and 'CBMC timed out' not in text
 if not accepted:
  cleanup=[]
  for q in (B/'NCD_tmp').rglob('*'):
   if q.is_file() and (q.name.startswith('external-sat') or q.name.startswith('smt2_dec_problem')):cleanup.append(dict(path=str(q),bytes=q.stat().st_size));q.unlink()
  (B/(a+'-solver-cleanup.json')).write_text(json.dumps(cleanup)+'\n')
 status='terminal' if not accepted else 'running'
 (B/('NCD_native_'+tag+'_state.json')).write_text(json.dumps(dict(status=status,report=report),indent=2)+'\n')
 if not accepted:raise SystemExit('STOP failed shape '+a)
(B/('NCD_native_'+tag+'_state.json')).write_text(json.dumps(dict(status='terminal',report=report),indent=2)+'\n')
