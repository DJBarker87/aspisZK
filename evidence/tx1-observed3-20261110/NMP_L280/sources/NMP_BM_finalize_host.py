"""Own final evidence validation/export; no compiler, launcher or checker changes."""
from pathlib import Path
import hashlib,json,shutil,sys
B=Path.cwd();mode=sys.argv[1];cfg=json.loads((B/sys.argv[2]).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,x):(B/n).write_text(json.dumps(x,indent=1)+'\n')
manifest=json.loads((B/'NMP_BM_MODULES.json').read_text())
def source_checks():
 rows=[]
 for m in manifest['modules']:
  rel='NMP_generated/'+m.replace('.','/')+'.lean';p=B/rel
  r=json.loads((B/manifest['selected_receipts'][m]).read_text());assert r['exit_status']==0,m
  snap=(B/manifest['selected_receipts'][m]).parent/'sources'/rel
  assert p.read_bytes()==snap.read_bytes(),m
  assert sha(p) in r['source_hashes'].values(),m
  rows.append(dict(module=m,source=rel,sha256=sha(p),receipt=manifest['selected_receipts'][m]))
 return rows
if mode=='export':
 rows=source_checks();dest=B/'NMP_BM_exports_20261107';dest.mkdir(exist_ok=False)
 objects=[]
 mods=manifest['modules']+['NMP_COMBINED_IMPORT','NMP_BM_Driver','NMP_BM_ProofDriver','NMT_CallTree','NMT_TransportBase','NMT_tx1.Types','NMT_RSL_Base','NMT_RSL_Verifier','NMT_RSL_TX1_136','NMT_RSL_TX1_137','NMT_RSL_TX1_087']
 for m in mods:
  stem=m.replace('.','/')
  assert (B/'NMP_objects'/(stem+'.olean')).is_file(),m
  for ext in ['.olean','.olean.private','.olean.server','.ir']:
   p=B/'NMP_objects'/(stem+ext)
   if not p.exists():continue
   q=dest/(stem+ext);q.parent.mkdir(parents=True,exist_ok=True);before=sha(p);shutil.copyfile(p,q);assert before==sha(q)==sha(p)
   objects.append(dict(module=m,path=str(q),source=str(p),sha256=before,bytes=q.stat().st_size))
 write('NMP_BM_EXPORT.json',dict(status='PASS',source_revision=cfg['source_revision'],destination=str(dest),objects=objects,sources=rows,row_roots=[],no_cache_deleted=True))
 print('Export PASS: copied and pinned current own/support objects; no cache deleted')
elif mode=='audit':
 groups=json.loads((B/'NMP_BM_AUDIT_ROOTS.json').read_text())['groups'];allresults=[];metrics=[]
 for i,names in enumerate(groups):
  p=B/f'NMP_BM_audit/proof{i}/proof{i}.json';r=json.loads(p.read_text());assert r['exit_status']==0 and str(r['swaps'])=='0',i
  assert {x['root'] for x in r['results']}==set(names) and len(r['results'])==len(names),i
  for x in r['results']:
   assert x['equal'] and sorted(x['collect_axioms'])==sorted(x['walked_axioms']),x['root']
   assert set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},x
   assert x['reachable_constants']>0,x
   allresults.append(x)
  metrics.append(dict(group=i,scope=f'NMP_L{171+i:03d}',target=names,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],print_axioms=r['print_axioms']))
 fixture=json.loads((B/'NMP_BM_audit/fixtures/fixtures.json').read_text())
 expected={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
 assert fixture['exit_status']==0 and len(fixture['results'])==8
 for x in fixture['results']:assert x['equal'] and x['collect_axioms']==x['walked_axioms']==expected[x['root']]
 scan=json.loads((B/'NMP_BM_audit/scan/scan.json').read_text());assert scan['exit_status']==0
 rows=[json.loads(l) for l in (B/'NMP_BM_LOADED_scan.jsonl').read_text().splitlines()]
 assert set(manifest['modules']+['NMP_COMBINED_IMPORT'])<={r['module'] for r in rows}
 assert all(r['imports_match'] and not r['dangling'] and not r.get('duplicate_owners') for r in rows)
 source_checks()
 write('NMP_AUDIT.json',dict(status='PASS_SUPPORT_ONLY',target_established=False,row_roots=[],source_revision=cfg['source_revision'],new_support_roots=len(manifest['roots']),headline='AspisR1.RPx_Deployed.deployed',raw_results=allresults,raw_metrics=metrics,nfx_exit=0,nfx_modules=len(rows),fixtures='8 expected planted/mutation results matched',new_trust_rows=[],kani_this_run=0))
 print('Audit PASS: raw collectors agree, standard axioms only, NFX0 and fixtures matched; no row credit')
elif mode=='retention':
 m=json.loads((B/'NMP_STAGING_MANIFEST.json').read_text());assert m['pool_revision']=='b936275465600469312d1f058cdc91ea2a11f3dc'
 assert all(sha(B/'NMP_emission_src'/n)==r['sha256'] for n,r in m['files'].items())
 pins=json.loads((B/'NMP_emitted/prepare/NMP_PINS.json').read_text());assert pins['exit']==pins['aeneas_exit']==pins['charon_exit']==0 and pins['lock_before']==pins['lock_after']
 for n,h in pins['outputs'].items():assert sha(B/'NMP_emitted/prepare'/n)==h,n
 imported=[]
 for file in ['NMP_BM_SEED_PINS.json','NMP_BM_RSL_OBJECT_PINS.json','NMP_BM_TRANSPORT_OBJECT_PINS.json']:
  for row in json.loads((B/file).read_text()):assert sha(Path(row['destination']))==row['sha256'];imported.append(row)
 fresh=['NMP_emission_src','NMP_extract_target','NMP_emitted','NMP_BM_audit','NMP_BM_exports_20261107']+[f'NMP_L{i:03d}'for i in range(81,281)]+['NMP_E001','NMP_E002']
 size=sum(p.stat().st_size for n in fresh for p in (B/n).rglob('*') if p.is_file())
 assert size<30_000_000_000,size
 write('NMP_RETENTION.json',dict(status='PASS',frozen_files=len(m['files']),frozen_lock_sha256=pins['lock_after'],fresh_named_outputs_bytes=size,imported_objects_checked=len(imported),source_revision=cfg['source_revision'],no_cache_deleted=True,no_key_cleanup=True,shipped_check=json.loads((B/'NMP_BM_SHIPPED_UNCHANGED.json').read_text())))
 print('Retention PASS: frozen sources/lock and imported object hashes unchanged; named outputs under30GB')
elif mode=='final':
 rs=[]
 for p in B.glob('NMP_L[0-9][0-9][0-9]/receipt.json'):
  if 81<=int(p.parent.name[-3:])<=280:rs.append(json.loads(p.read_text()))
 assert len(rs)==199,len(rs)
 assert {r['attempt'] for r in rs}=={f'NMP_L{i:03d}' for i in range(81,280)}
 assert json.loads((B/'NMP_AUDIT.json').read_text())['status']=='PASS_SUPPORT_ONLY'
 assert json.loads((B/'NMP_RETENTION.json').read_text())['status']=='PASS'
 source_checks()
 child=json.loads((B/'NMP_BM_CHILD136_FINAL.json').read_text())
 write('NMP_BM_FINAL.json',dict(status='BUDGET_END_SUPPORT_ONLY',target_established=False,closed_rows=[],candidate_roots=[],baseline='ledger24:581/0/18',kani=0,extraction_scopes=2,charged_L_scopes_after_this_scope=200,completed_L_scopes_before_this_scope=199,source_revision=cfg['source_revision'],child136_recheck=child,blocking_findings=['NMP-BM-S1:130 observer domain','NMP-BM-S2:179 all outcomes','NMP-BM-S3:y1 canonicality','NMP-BM-S4:begin Err projection','concrete full-observation CLOSED-library interpretation/domain discharge'],next='Compose the checked emitted bodies with the concrete complete canonical library packets; instantiate the canonical136 root when available. No whole-parent Kani route.'))
 print('Final PASS:200 charged scopes accounted for; target not established; no row promotion')
else:raise ValueError(mode)
