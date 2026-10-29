from pathlib import Path
import hashlib,json
D=Path('/home/dombarker/project-offloads/codex-pv-diag4-20261029');P=D.parent/'codex-pv-diag3-20261029';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((P/'project-resolution.json').read_text())['modules'];rows=json.loads((P/'resume-cache-preflight.json').read_text())['rows'];needed=set();b=json.loads((D/'sampler-generation-chain.json').read_text())['sources']
roots=['R1Z.PV_RunJoin_CompletedWorld','R1Z.PV_RunJoin_SourceBinding','R1Z.PV_RunJoin_UnifiedRetry']
def visit(m):
 if m in needed:return
 needed.add(m)
 for dep in pins[m]['imports'] if m in pins else rows[m].get('record_dependencies',{}):visit(dep)
for m in roots:visit(m)
assert 'R1Z.PrivacyR1HeadlineV2' not in needed
for m in needed:
 r=rows[m];assert sha(Path(r['path']))==r['sha256'],m
 if m in pins:assert r.get('source_sha256')==pins[m]['sha256'],m
 if m in b:assert r.get('source_sha256')==b[m]['sha256'],m
 for dep,d in r.get('record_dependencies',{}).items():assert d['sha256']==rows[dep]['sha256'],(m,dep)
 if r['authority']=='h4 external' or m in roots:continue
 obj=D/'objects'/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 if not obj.exists():obj.symlink_to(r['path'])
for m in roots:
 s=D/'sources'/(m.replace('.','/')+'.lean');s.parent.mkdir(parents=True,exist_ok=True);s.write_bytes((D/'source-inputs'/(m+'.lean.txt')).read_bytes());assert sha(s)==pins[m]['sha256']
(D/'extra-consumer-preflight.json').write_text(json.dumps(dict(roots=roots,checked=len(needed),rows={m:rows[m] for m in needed},mismatches=[]),indent=2)+'\n');print('extra roots',len(roots),'checked',len(needed))
