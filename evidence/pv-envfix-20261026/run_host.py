"""One private, serial env-J compile; invoke with attempt and slash module.
Path-only launcher copy; retained shared inputs are read-only.
"""
import pathlib,sys,json,subprocess,hashlib,re,time
B=pathlib.Path('/home/dombarker/project-offloads');P=B/'codex-pv-envfix-20261026';E=P/'evidence'
a=int(sys.argv[1]);m=sys.argv[2];assert 35900<=a<=36199
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (E/f'receipt-{a}.json').exists()
assert not (B/f'aspis-fs-generic-20261006/evidence/out-{a}.log').exists()
assert not (E/f'out-{a}.log').exists()
# Persist admission stdout/stderr even if the reservation helper fails.
rp=E/f'reservation-{a}.json';rl=E/f'reservation-{a}.log'
with rl.open('w') as f:
 rc=subprocess.run(['python3',str(B/'codex-cx-s2x-20261023/S2X_reservation.py'),str(rp)],stdout=f,stderr=subprocess.STDOUT).returncode
if not rp.exists():
 print('MISSING RESERVATION JSON; retry helper once after 30 seconds');sys.exit(79)
r=json.loads(rp.read_text())
if not r.get('allowed'):
 (E/f'refusal-{a}.json').write_text(json.dumps(dict(attempt=a,charged=False,admission=r,exit=rc),indent=2)+'\n')
 print('RESERVATION REFUSED',rc,r);sys.exit(78 if rc in (0,78) else rc)
env=json.loads((P/'env/J.json').read_text());paths=[P/'objects']+[pathlib.Path(p) for p in env['LEAN_PATH'].split(':')]
src=P/'sources'/(m+'.lean');text=src.read_text();deps=[]
for line in text.splitlines():
 if line.startswith('import '):
  for n in line.split()[1:]:
   n=n.replace('.','/');obj=next((p/(n+'.olean') for p in paths if (p/(n+'.olean')).is_file()),None)
   assert obj is not None, f'missing {n}'
   deps.append(dict(module=n,path=str(obj),sha256=sha(obj)))
fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
cmd=['sh',str(P/'run-private.sh'),str(a),m,'J','7000','8',fp]
start=time.monotonic()
with (E/f'launcher-{a}.log').open('w') as f:outer=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT).returncode
op=E/f'out-{a}.log';tp=E/f'time-{a}.log'
if not tp.exists():
 print('LAUNCHER REFUSAL',outer,(E/f'launcher-{a}.log').read_text());sys.exit(outer or 78)
o=op.read_text();t=tp.read_text()
def val(p):
 z=re.search(p,t);return z[1].strip() if z else None
axioms=[' '.join(z.split()) for z in re.findall(r"^('[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms))",o,re.M|re.S)]
exit=int(val(r'Exit status:\s*(\d+)'))
allowed={'propext','Classical.choice','Quot.sound'}
bad=[z for z in axioms if '[' in z and not set(z.split('[',1)[1].rstrip(']').replace(' ','').split(','))<=allowed]
obj=P/'objects'/(m+'.olean')
r=dict(attempt=a,module=m,source_sha256=sha(src),source_revision=(P/'revision.txt').read_text().strip(),source_repository_path='docs/research/v8-r0-zk-20261009/lean/'+m+'.lean',deps=deps,deps_fingerprint=fp,command=cmd,launcher_sha256=sha(P/'run-private.sh'),env_sha256=sha(P/'env/J.json'),exit=exit,validation_exit=90 if bad else exit,outer_exit=outer,wall_seconds=time.monotonic()-start,wall=val(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),peak_rss_kib=int(val(r'Maximum resident set size \(kbytes\):\s*(\d+)')),swaps=int(val(r'Swaps:\s*(\d+)')),axioms=axioms,errors=[l for l in o.splitlines() if 'error:' in l],nonstandard_axioms=bad,admission=json.loads(rp.read_text()),caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000),object_sha256=sha(obj) if exit==0 and obj.exists() else None,object_bytes=obj.stat().st_size if exit==0 and obj.exists() else None)
(E/f'receipt-{a}.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));sys.exit(r['validation_exit'])
