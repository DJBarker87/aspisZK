"""Strict final artifact gate and mutations; no theorem or native proof credit."""
from pathlib import Path
import json,hashlib,lzma,copy,ast,subprocess
E=Path(__file__).resolve().parent
J=lambda n:json.loads((E/n).read_text())
a=J('NIB_AUDIT.json');d=J('NIB_LEDGER_DELTA.json');b=J('NIB_BUDGET.json')
expected=J('NIB_AUDIT_ROOTS.json')['roots']
def gate(a,d,b):
 assert a['status']=='PASS' and a['standard_axioms_only']
 assert a['root_count']==len(expected) and [r['root'] for r in a['roots']]==expected
 assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in a['roots'])
 assert a['all_batches_same_binary'] and a['walker']['byte_identical']
 assert len(a['fixture_results'])==8 and all(r['equal'] for r in a['fixture_results'])
 assert [r['walked_axioms'] for r in a['fixture_results']]==[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]]
 assert a['scan']['status']=='PASS' and a['scan']['dangling']==a['scan']['incompatible_owners']==a['scan']['import_mismatches']==0
 assert d['rows']==[] and d['composed_rows_added']==d['closed_by_this_job']==0
 assert d['before']==d['after'] and d['plan_theorem_status']=='OPEN' and d['model_subtheorem_status']=='PROVED-conditional'
 assert d['trust_added']==d['trust_removed']==[]
 assert b['Lean_scopes']<=50 and b['Kani']==b['extraction']==0

gate(a,d,b)
mutations=[('nonstandard axiom',0,lambda x:x['roots'][0]['walked_axioms'].append('sorryAx')),('missing root',0,lambda x:x['roots'].pop()),('missed planted axiom',0,lambda x:x['fixture_results'][0].__setitem__('walked_axioms',[])),('import mismatch',0,lambda x:x['scan'].__setitem__('import_mismatches',1)),('different binary',0,lambda x:x.__setitem__('all_batches_same_binary',False)),('false Pool promotion',1,lambda x:x.__setitem__('closed_by_this_job',1)),('false plan closure',1,lambda x:x.__setitem__('plan_theorem_status','CLOSED')),('new trust',1,lambda x:x['trust_added'].append('RuntimeCpiReadonlyEntry7')),('exceeded budget',2,lambda x:x.__setitem__('Lean_scopes',51))]
results=[]
for name,i,mutate in mutations:
 args=copy.deepcopy([a,d,b]);mutate(args[i])
 try:gate(*args)
 except AssertionError:results.append(dict(name=name,rejected=True))
 else:raise AssertionError(name)
for p in E.glob('NIB_*.py'):ast.parse(p.read_text(),filename=str(p))
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
for name in ['NIB_CLOSURE_PINS.json','NIB_L018_scan.jsonl']:
 raw=lzma.decompress((E/(name+'.xz')).read_bytes());assert hashlib.sha256(raw).hexdigest()==(E/(name+'.sha256')).read_text().strip()
for mod,num in [('NIB_Emission','002'),('NIB_Association','003'),('NIB_ReadToSettlement','004'),('NIB_FrameValues','011'),('NIB_EmissionFrame','012'),('NIB_COMBINED_IMPORT','013')]:
 snapshot=E/('NIB_L'+num)/'sources/NIB_generated'/(mod+'.lean')
 assert snapshot.read_bytes()==(E/(mod+'.lean')).read_bytes()
 assert J('NIB_L'+num+'/receipt.json')['exit_status']==0
assert not subprocess.check_output(['git','diff','--name-only','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs'],text=True)
(E/'NIB_TESTS.json').write_text(json.dumps(dict(positive=True,mutations=results,all_rejected=True,source_snapshots_match=True,shipped_sources_frozen=True,size_limit_pass=True),indent=1)+'\n')
print('PASS;',len(results),'mutations rejected; exact source snapshots; frozen shipped source')
