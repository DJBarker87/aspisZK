"""Focused immutable STX-cohort statement compilation; no provider replay."""
import pathlib,subprocess,json,shlex,sys,time,lzma,hashlib
E=pathlib.Path('evidence/pv-lib-20261107/lane-SLICE')
H='/home/dombarker/project-offloads/codex-pv-lib-slice-20261107'
host='dombarker@100.108.41.90'
a=int(sys.argv[1]);m=sys.argv[2];assert 49920<=a<=49999
assert not (E/f'turn-{a}.json').exists()
p=pathlib.Path('lean',m+'.lean');source=p.read_text()
assert source==subprocess.check_output(['git','show',':'+str(p)],text=True)
t=time.time();q=subprocess.run(['ssh',host,'STREAMB_SLOTS=3 /home/dombarker/streamb-slots/turn.sh'],text=True,capture_output=True)
turn=dict(attempt=a,exit=q.returncode,wall=time.time()-t,stdout=q.stdout,stderr=q.stderr)
(E/f'turn-{a}.json').write_text(json.dumps(turn,indent=2)+'\n');assert q.returncode==0
payload=dict(attempt=a,module=m,source=source,script=(E/'session4-host.py').read_text(),authority=(E/'STX_OBJECT_AUTHORITY.json.xz').read_bytes().hex(),revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
wrapper='''import pathlib,json,sys,subprocess,re,os
x=json.load(sys.stdin);P=pathlib.Path("/home/dombarker/project-offloads/codex-pv-lib-slice-20261107");a=x['attempt']
pattern=re.compile(r'(^|[-_])'+str(a)+r'([-_.]|$)');hits=[]
for job in P.parent.glob('codex-*'):
 for d,dirs,names in os.walk(job/'evidence'):
  for n in names:
   if pattern.search(n) and os.path.isfile(os.path.join(d,n)):hits.append(os.path.join(d,n))
assert not hits,hits
(P/'evidence'/f'id-audit-{a}.json').write_text(json.dumps(dict(attempt=a,hits=hits)))
(P/'sources-stx4').mkdir(exist_ok=True)
(P/'sources-stx4'/(x['module']+'.lean')).write_text(x['source'])
(P/'STX_OBJECT_AUTHORITY.json.xz').write_bytes(bytes.fromhex(x['authority']))
(P/'session4-host.py').write_text(x['script'])
sys.exit(subprocess.call([sys.executable,str(P/'session4-host.py'),str(a),x['module'],x['revision'],'stx']))
'''
r=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(wrapper)],input=json.dumps(payload),capture_output=True,text=True)
(E/f'transport-{a}.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n')
for kind,suffix in [('id-audit','json'),('receipt','json'),('out','log'),('time','log'),('admission','json'),('admission','log'),('resolution','json.xz')]:
 q=subprocess.run(['ssh',host,f'cat {H}/evidence/{kind}-{a}.{suffix}'],capture_output=True)
 if q.returncode==0:(E/f'{kind}-{a}.{suffix}').write_bytes(q.stdout)
if r.returncode!=0:
 (E/f'failed-input-{a}.lean.xz').write_bytes(lzma.compress(source.encode()))
print(r.stdout[-7000:]);print(r.stderr[-2000:]);sys.exit(r.returncode)
