"""Scoped immutable-source preparation; no compiler or host access."""
import json,pathlib,hashlib,sqlite3,subprocess,resource,time
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/port35anchor-20261025';O=pathlib.Path('/private/tmp/Port35ANCHOR-20261025');O.mkdir(mode=0o700,exist_ok=True)
def pin(p):
 p=pathlib.Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return {'path':str(p),'bytes':p.stat().st_size,'sha256':h.hexdigest()}
def key(n):return json.dumps(n,separators=(',',':'),ensure_ascii=False)
start=time.monotonic();ip=E/'Port35ANCHOR_scoped-inventory.json';ip=ip if ip.exists() else O/ip.name;j=json.loads(ip.read_text())
if ip.parent==E and ip.stat().st_size>5000000:
 (O/'Port35ANCHOR_scoped-inventory.json').write_text(json.dumps(j,separators=(',',':'))+'\n');(E/'Port35ANCHOR_scoped-inventory.json').unlink()
origins=sorted({r[1] for r in j['selected']});s={'origins':origins,'roots':j['roots'],'choices':[[r[0],origins.index(r[1])] for r in j['selected']]};(E/'Port35ANCHOR_selection.json').write_text(json.dumps(s,separators=(',',':'))+'\n')
g=json.loads((E/'Port35ANCHOR_ref-Port32CONSUMER_groups.json').read_text());g=[r for r in g if r[0] in origins]
for r in g:
 for i,label in enumerate(['CURRENT:BASE:ExtractedOpeningQueriesModel:part0','CURRENT:INCREMENTAL:Query31ArrayReadback:part0','CURRENT:INCREMENTAL:Query31DigestInputBridge:part0','CURRENT:INCREMENTAL:Query31SourceCalls:part0','CURRENT:INCREMENTAL:Query31SourceOracleBridge:part0']):
  if i>0 and r[0]==label:r[1]=f'/private/tmp/Port34RAW-361-20261025/Port34RAW-part{i}.olean'
assert {r[0] for r in g}==set(origins)
(E/'Port35ANCHOR_groups.json').write_text(json.dumps(g,separators=(',',':'))+'\n')
pre=json.loads((E/'Port35ANCHOR_reused-attempt-361.json').read_text())['fresh'];runtime=pre['runtime'];api=pre['api']
for p in runtime+api:assert pin(p['path'])==p
r={'status':'scoped preparation, data only','selection':pin(E/'Port35ANCHOR_selection.json'),'groups':pin(E/'Port35ANCHOR_groups.json'),'inputs':[pin(p) for _,p in g],'runtime':runtime,'api':api,'sysroot':pre['sysroot'],'inventory_metadata':pin(O/'Port35ANCHOR_scoped-inventory.json'),'inventory_assessment':'355 SQLite exact-name queries only; inventory whole-file hash reused, not rehashed; Port32 choices retained. Five released361 exact-CI exports replace containing parts, same chosen origins. Conflicts NEW re-pin. No whole-factor identity.','selected':len(j['selected']),'project':sum(not r[1].startswith('CORE:') for r in j['selected']),'origins':len(g),'raw_bytes':sum(pathlib.Path(p).stat().st_size for _,p in g),'wall_seconds':time.monotonic()-start,'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'swaps':resource.getrusage(resource.RUSAGE_SELF).ru_nswap,'lean_calls':0}
assert r['peak_rss_bytes']<512*1024**2
(E/'Port35ANCHOR_inputs.json').write_text(json.dumps(r,indent=2)+'\n');print({k:r[k] for k in ['selected','project','origins','raw_bytes','wall_seconds','peak_rss_bytes']})
