"""Check the two fresh claims and freeze their once-only focused audit."""
import pathlib,json,hashlib,re,sys
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume9';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
proofs=[]
for a,m,n in [(40208,'PV_RE_InstalledOp84B9','installed_noCatch'),(40209,'PV_RE_ReserveGuards9','client_to_store')]:
 r=json.load(open(E/f'receipt-{a}.json'));assert r['accepted'] and len(r['modules'])==1
 row=r['modules'][0];p=L/(m+'.lean');s=p.read_text();assert row['source']['sha256']==sha(p)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|implemented_by)\b',s)
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',s)
 full='R1Z.'+m+'.'+n;assert any("'"+full+"'" in x for x in row['axioms'])
 assert all(not re.search(r'\b(?:sorryAx|Lean\.ofReduceBool)\b',x) for x in row['axioms'])
 proofs.append(dict(module='R1Z.'+m,declaration=full,path=str(p.relative_to(R)),source_sha256=sha(p),attempt=a,object_sha256=row['object_sha256'],axioms=row['axioms']))
# Identical binders/conclusion, a separately named namespace and proof only.
def statement(p):return p.read_text().split('theorem installed_noCatch',1)[1].split(':= by',1)[0]
assert statement(L/'PV_RE_InstalledOp84.lean')==statement(L/'PV_RE_InstalledOp84B9.lean')
manifest=dict(proofs=proofs,original_failed_candidate=dict(module='R1Z.PV_RE_InstalledOp84',attempt=40207,unchanged_sha256=sha(L/'PV_RE_InstalledOp84.lean'),same_statement_as_replacement=True,credit=False),audits=[dict(attempt=40297+i,module='R1Z.PV_RE_FinalAudit9'+x,path=str((L/('PV_RE_FinalAudit9'+x+'.lean')).relative_to(R)),sha256=sha(L/('PV_RE_FinalAudit9'+x+'.lean'))) for i,x in enumerate('ABC')],scope='focused claims and smaller native fixture statement audit; not a release replay; no V404/V405 closure',external_authority='resume7/external-object-manifest.json',external_manifest_sha256=sha(E.parent/'resume7/external-object-manifest.json'),h4_preflight_sha256=sha(E/'h4-verification.json'))
p=E/'frozen-proof-manifest.json'
if '--check' in sys.argv:assert json.load(open(p))==manifest
else:p.write_text(json.dumps(manifest,indent=2)+'\n')
print('Two fresh claims frozen; original failed candidate unchanged; audit IDs 40297–40299.')
