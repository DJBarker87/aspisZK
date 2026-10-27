from pathlib import Path
import subprocess,json,hashlib,re,time,shlex
P=Path(__file__).resolve().parent;HOST='dombarker@100.108.41.90';ROOT='/home/dombarker/project-offloads/aspis-joint-20261019';T='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence';LAUNCH='/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh';OWN='/home/dombarker/project-offloads/codex-pv-recount5-20261027'
def ssh(cmd,data=None):return subprocess.run(['ssh',HOST,cmd],input=data,capture_output=True)
ssh('mkdir -p '+OWN)
receipts=json.loads((P/'receipts.json').read_text()) if (P/'receipts.json').exists() else [];attempt=max([r['attempt'] for r in receipts]+[54199])+1
revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()
for check in json.loads((P/'checks.json').read_text()):
 if any(r['module']==check['module'] for r in receipts):continue
 if sum(r['compiler_invoked'] for r in receipts)>=20:break
 for retry in range(11):
  a=attempt;attempt+=1
  pre=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2x-20261023/S2X_reservation.py {OWN}/reservation-{a}.json > {OWN}/reservation-{a}.log 2>&1; cat {OWN}/reservation-{a}.log; cat {OWN}/reservation-{a}.json')
  (P/f'reservation-{a}.log').write_bytes(pre.stdout+pre.stderr)
  if b'"allowed": false' in pre.stdout.lower():
   receipts.append(dict(attempt=a,module=check['module'],compiler_invoked=False,reason='preflight reservation refusal'));(P/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(a,'reservation refusal',flush=True);time.sleep(183);continue
  if b'"allowed": true' not in pre.stdout.lower():raise RuntimeError(pre.stdout+pre.stderr)
  mods=list(dict.fromkeys(m for m,n in check['items']));hashes=ssh('sha256sum '+' '.join(ROOT+'/sources/'+m.replace('.', '/')+'.lean '+ROOT+'/objects/'+m.replace('.', '/')+'.olean' for m in mods))
  (P/(check['module']+'-inputs.txt')).write_bytes(hashes.stdout+hashes.stderr);fp=hashlib.sha256(hashes.stdout).hexdigest()
  s=(P/check['source']).read_bytes();put=ssh('test ! -e '+ROOT+'/sources/'+check['module']+'.lean && cat > '+ROOT+'/sources/'+check['module']+'.lean',s) if retry==0 else None
  if put is not None:assert put.returncode==0,put.stderr
  cmd=f'sh {LAUNCH} {a} {check["module"]} J 7000 8 {fp}';result=ssh(cmd);(P/f'launcher-{a}.log').write_bytes(result.stdout+result.stderr)
  raw=ssh(f'cat {T}/out-{a}.log');tim=ssh(f'cat {T}/time-{a}.log')
  (P/f'out-{a}.log').write_bytes(raw.stdout+raw.stderr);(P/f'time-{a}.log').write_bytes(tim.stdout+tim.stderr)
  compiler=b'Exit status:' in tim.stdout;ts=tim.stdout.decode();outs=raw.stdout.decode()
  def metric(label):
   m=re.search(re.escape(label)+r':\s*(.+)',ts);return m[1].strip() if m else None
  r=dict(shared_source_matches_pinned=check['pinned_sha256'] in hashes.stdout.decode(),pinned_ref=check['pinned_ref'],pinned_path=check['pinned_path'],pinned_sha256=check['pinned_sha256'],attempt=a,module=check['module'],source_sha256=check['sha256'],source_revision=revision,dependency_fingerprint=fp,command=cmd,launcher_exit=result.returncode,compiler_invoked=compiler,exit=metric('Exit status'),wall=metric('Elapsed (wall clock) time (h:mm:ss or m:ss)'),peak_RSS_KiB=metric('Maximum resident set size (kbytes)'),swap=metric('Swaps'),axioms=[l for l in outs.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l],errors=[l for l in outs.splitlines() if 'error:' in l],limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=128,Lean_M=7000),log=f'out-{a}.log',time=f'time-{a}.log')
  receipts.append(r);(P/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(a,check['module'],'compiler',compiler,'exit',r['exit'],'errors',len(r['errors']),flush=True)
  if not compiler and (b'HOLD' in result.stdout or result.returncode==78):time.sleep(183);continue
  if not compiler and b'already sent in env J' in result.stdout:break
  if not compiler:raise RuntimeError(result.stdout+result.stderr)
  break
 else:raise RuntimeError('ten retries exhausted; return to compile-free work')
print('Complete',flush=True)
