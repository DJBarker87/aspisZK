"""Input staging, pinned-cache checks and serial capped focused compile."""
import pathlib,json,sys,hashlib,subprocess,time,re,os,lzma
B=pathlib.Path('/home/dombarker/project-offloads/codex-pv-int-20261106');L=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-20261107');P=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107');E=P/'evidence';E.mkdir(exist_ok=True)
x=json.load(sys.stdin);a=x['attempt'];m=x['module'];audit=x['audit']
assert ((49600<=a<=49689 or 49900<=a<=49999) and not audit) or (49690<=a<=49699 and audit)
assert x['turn']['exit']==0 and x['turn']['attempt']==a
sha=lambda p:hashlib.file_digest(open(p,'rb'),'sha256').hexdigest()
for p in E.glob('refusal-*.json'):assert time.time()-json.load(open(p))['epoch']>=180
pattern=re.compile(r'(^|[-_])'+str(a)+r'([-_.]|$)');hits=[]
for job in B.parent.glob('codex-*'):
 for d,dirs,names in os.walk(job/'evidence'):
  for n in names:
   if pattern.search(n) and os.path.isfile(os.path.join(d,n)):hits.append(os.path.join(d,n))
sent=B.parent/'r1-privacy-build-integration-20261019/evidence/sent.txt';lines=[l for l in sent.read_text().splitlines() if len(l.split())>2 and l.split()[2]==str(a)]
assert not hits and not lines,(hits,lines)
(E/f'id-audit-{a}.json').write_text(json.dumps(dict(attempt=a,hits=hits,sent=lines)))
# Baseline is the integration job's audited final build instance (D937).
reuse=json.loads(lzma.decompress((B/'evidence/reuse-validation.json.xz').read_bytes()))
expected={m:r['accepted'] for m,r in reuse['checks'].items() if m in reuse['reuse']}
invalid=set(json.load(open(B/'evidence/invalidated-attempts.json')))
for p in sorted((B/'evidence').glob('results-*.json')):
 if int(p.stem.split('-')[-1]) not in invalid:
  for r in json.load(open(p)):
   if r['accepted']:expected[r['module']]=r
source_sha=hashlib.sha256(x['source'].encode()).hexdigest()
for p in list((L/'evidence').glob('receipt-*.json'))+list(E.glob('receipt-*.json')):
 r=json.load(open(p))
 if r['target']==m and not r['accepted']:assert r['source_sha256']!=source_sha,'unchanged failed source'
 if r['accepted'] and not r['runtime_audit']:expected[r['target']]=r
external={r['module'].replace('/','.'):r for r in json.load(open(B/'evidence/external-authority.json'))}
resolved={}
def check(d):
 if d in resolved:return
 rel=d.replace('.','/');o=(P/'objects'/(rel+'.olean')) if (P/'objects'/(rel+'.olean')).exists() else ((L/'objects'/(rel+'.olean')) if (L/'objects'/(rel+'.olean')).exists() else B/'objects'/(rel+'.olean'))
 if d in expected:
  r=expected[d];assert sha(o)==r['object_sha256'],('object changed',d)
  s=(P/'sources'/(rel+'.lean')) if (P/'sources'/(rel+'.lean')).exists() else ((L/'sources'/(rel+'.lean')) if (L/'sources'/(rel+'.lean')).exists() else B/'sources'/(rel+'.lean'));assert sha(s)==r['source_sha256'],('source changed',d)
  deps=r.get('dependency_hashes') or {k:v['sha256'] for k,v in r.get('dependencies',{}).items()}
  resolved[d]=dict(path=str(o),sha256=sha(o),source_sha256=sha(s))
  for dep,want in deps.items():
   check(dep);assert resolved[dep]['sha256']==want,('dependency cohort mismatch',d,dep)
 elif d in external:
  r=external[d];q=B/'external'/(rel+'.olean');assert not o.exists(),('external shadow',d)
  assert sha(q)==r['object_sha256'],('external changed',d)
  resolved[d]=dict(path=str(q),sha256=sha(q))
 else:raise RuntimeError('not in coherent cohort: '+d)
deps=re.findall(r'^import (\S+)',x['source'],re.M)
for d in deps+x.get('runtime_modules',[]):check(d)
# The external authority is checked in full before loading any external object.
for d in external:check(d)
resolution=dict(modules=resolved,cohort='D937 combined 92 CLOSED rows',LEAN_PATH=str(P/'objects')+':'+str(L/'objects')+':'+str(B/'objects')+':'+str(B/'external'))
(E/f'resolution-{a}.json').write_text(json.dumps(resolution))
s=P/'sources'/(m.replace('.','/')+'.lean');o=P/'objects'/(m.replace('.','/')+'.olean')
if audit:
 assert m in expected and expected[m]['source_sha256']==source_sha,'audit only the compiled exact driver source'
else:
 assert m not in expected,'do not overwrite an accepted object; use a new module'
s.parent.mkdir(exist_ok=True);o.parent.mkdir(exist_ok=True);s.write_text(x['source'])
env=json.load(open(B/'J.json'));env['LEAN_PATH']=str(P/'objects')+':'+str(L/'objects')+':'+env['LEAN_PATH'];(P/'J.json').write_text(json.dumps(env));assert subprocess.check_output([env['LEAN'],'--githash'],text=True).strip()==env['LEAN_GITHASH']
cmd=['systemd-run','--user','--scope','--quiet',f'--unit=pv-lib-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(E/f'time-{a}.log'),'timeout','600','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',str(P/'J.json'),str(P/'objects'),str(P/'sources'),str(o),str(s),'7000']
if audit:
 (P/'run-thread-audit.py').write_text(x['audit_wrapper'])
 cmd=cmd[:cmd.index('timeout')]+['timeout','600','python3',str(P/'run-thread-audit.py'),str(P/'J.json'),str(s)]
intent=dict(runtime_audit=audit,attempt=a,target=m,source_revision=x['source_revision'],source_index_blob=x.get('source_index_blob'),source_path=x['source_path'],source_sha256=source_sha,stream_b_turn=x['turn'],dependencies={d:resolved[d] for d in deps},command=cmd,resolution_sha256=sha(E/f'resolution-{a}.json'))
(E/f'submission-{a}.json').write_text(json.dumps(intent,indent=2))
with (E/f'admission-{a}.log').open('w') as f:
 rc=subprocess.call(['python3',str(B.parent/'codex-pv-runjoin-20261026/reservation-existing.py'),str(E/f'admission-{a}.json')],stdout=f,stderr=subprocess.STDOUT)
admit=json.load(open(E/f'admission-{a}.json'))
if rc!=0 or admit.get('allowed') is not True:
 (E/f'refusal-{a}.json').write_text(json.dumps(dict(epoch=time.time(),compiler_started=False,admission=admit,exit=rc)))
 print('REFUSED: next ID after 180 seconds');sys.exit(78)
with (E/f'out-{a}.log').open('w') as f:rc=subprocess.call(cmd,stdout=f,stderr=subprocess.STDOUT,cwd=P)
out=(E/f'out-{a}.log').read_text();tim=(E/f'time-{a}.log').read_text()
for key,pat in dict(exit=r'Exit status: (\d+)',peak_rss_kbytes=r'Maximum resident set size \(kbytes\): (\d+)',swaps=r'Swaps: (\d+)',wall=r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)').items():
 match=re.search(pat,tim);intent[key]=match[1] if match else None
intent.update(accepted=rc==0 and intent['exit']=='0' and 'error:' not in out and 'sorryAx' not in out,launcher_exit=rc,axioms_summary_based=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out))
if intent['accepted'] and not audit:intent['object_sha256']=sha(o)
(E/f'receipt-{a}.json').write_text(json.dumps(intent,indent=2))
print(json.dumps({k:intent[k] for k in ['attempt','target','accepted','exit','wall','peak_rss_kbytes','swaps']}));print(out[-12000:])
sys.exit(0 if intent['accepted'] else 1)
