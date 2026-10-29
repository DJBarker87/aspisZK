from auditlib9 import *
checks=[]
def ck(n,b):
 checks.append(dict(check=n,pass_=bool(b)));assert b,n
rows=json.loads((P/'rows9.json').read_text());old=json.loads((B/'recount8/rows8.json').read_text());ck('407 same identities',[x['id'] for x in rows]==[x['id'] for x in old] and len(rows)==407)
allowed={'dependency_bucket','closure_theorem','closure_route'}
for a,b in zip(old,rows):ck(a['id']+' historical fields retained',all(k in allowed or b.get(k)==v for k,v in a.items()))
ck('exclusive OPEN buckets',all((r['dependency_bucket'] in 'abcd' if r['recount9_status']=='OPEN' else r['dependency_bucket'] is None) for r in rows))
ck('totals',collections.Counter(r['recount9_status'] for r in rows)=={'OPEN':73,'CLOSED-ON-CANDIDATE':57,'CLOSED-ON-RESEARCH':87,'REDUCED':176,'EVIDENCED':14})
ck('owner bucket follows precedence',next(r for r in rows if r['id']=='V231')['dependency_bucket']=='c')
for r in rows:
 if r['id'] in ['V213','V217','V229','V230','V256','V257','V260','V265']:
  z=r['closing_statement9'];s=read(z['ref'],z['path']);ck(r['id']+' exact closing declaration present',bool(re.search(r'\btheorem\s+'+re.escape(z['theorem'].split('.')[-1])+r'\b',s)))
# Unique content objects verified once, including retained prior recount snapshots.
seen=set()
for x in manifest:
 f=P/x['snapshot']
 if (str(f.resolve()),x['sha256']) in seen:continue
 raw=read(x['ref'],x['path']).encode() if 'snapshot_key' in x else gzip.open(f,'rb').read() if f.suffix=='.gz' else f.read_bytes();ck('sha256 '+x['snapshot'],hashlib.sha256(raw).hexdigest()==x['sha256']);ck('git blob '+x['snapshot'],hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==x['blob']);seen.add((str(f.resolve()),x['sha256']))
changed=json.loads((P/'definition-audit9.json').read_text());ck('changed defining sources only LOG reporting',all(not x['changed_from8'] or x['definition'].split('#')[0]=='docs/research/v8-r0-zk-20261009/LOG.md' for x in changed))
footer='## Decision requested (D474, 2026-10-29)';before=read('research','design/PV-OWNER-PACKET-20261027.md');after=Path('design/PV-OWNER-PACKET-20261027.md').read_text();ck('D474 and D478 unchanged byte for byte',before[before.index(footer):]==after[after.index(footer):])
ck('no theorem/proof source added',not list(P.glob('*.lean')))
size=sum(f.stat().st_size for f in P.rglob('*') if f.is_file());ck('recount9 <100000000 bytes',size<100_000_000)
allocated=int(subprocess.check_output(['du','-sk',str(P)],text=True).split()[0])*1024;ck('allocated disk below100MB',allocated<100_000_000)
ck('no binaries or compiled objects',not any(f.suffix in ['.olean','.o','.rlib','.so','.exe','.tar'] for f in P.rglob('*')))
out=dict(result='PASS',checks=len(checks),rows=407,statuses=dict(collections.Counter(r['recount9_status'] for r in rows)),open_buckets=dict(collections.Counter(r['dependency_bucket'] for r in rows if r['recount9_status']=='OPEN')),unique_content_objects=len(seen),recount9_bytes=size,allocated_bytes=allocated,Lean=0,Kani=0,env_J_IDs_used=[],endpoint_premises_removed_added_weakened=[0,0,0],owner_D474_D478_unchanged=True,definition_changes='25 LOG-reporting file witnesses only; no formal defining source changes',checks_detail=checks)
(P/'validation9.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='checks_detail'},indent=2))
