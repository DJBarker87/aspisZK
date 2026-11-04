"""Add coherent-import checks to NFG without changing inherited admission."""
from pathlib import Path
import json,hashlib,subprocess,sys,copy,resource,time
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;O=E.parent/'slice-q-compose6-20261104'
sys.path.insert(0,str(O));import NFG_validate as prior
obj=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ROWS=['TX1:181','TX2:104'];ROOT='crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range'
def own_checks(audit=None):
 audit=obj(E/'NFN_AUDIT.json') if audit is None else audit
 assert audit['status']=='PASS_COMBINED_GEOMETRY_HEADLINE_NFG'
 assert audit['standard_axioms_only'] and audit['raw_graphs_equal_collectAxioms'] and audit['zero_unresolved_constants']
 assert audit['headline']=='AspisR1.RPx_Deployed.deployed'
 assert audit['combined_source_sha256']==sha(E/'NFN_COMBINED_IMPORT.lean')
 assert audit['driver_source_sha256']==sha(E/audit.get('driver_file','NFN_Driver.lean'))
 assert audit['walker_identity']==obj(E/'NFN_WALKER_IDENTITY.json')
 conf=obj(E/'NFN_AX2_CONFORMANCE.json');assert conf['status']=='PASS' and conf['unchanged_pre_runtime_prefix'] and conf['unchanged_raw_audit_action']
 assert audit['ax2_conformance_sha256']==sha(E/'NFN_AX2_CONFORMANCE.json')
 assert conf['driver_sha256']==audit['driver_source_sha256']
 assert conf['diff_sha256']==sha(E/conf['diff'])
 final=obj(E/'NFN_L070/receipt.json');assert final['exit_status']==0
 assert final['source_hashes']['NFN_generated/NFN_ProofDriver.lean']==conf['driver_sha256']
 adm=obj(E/'NFN_L070-admission.json');assert adm['exit']==0 and adm['reservation']['allowed'] is True
 scan=audit['incoherence_scan'];assert all(scan[k]==0 for k in ['dangling','duplicate_owners','import_mismatches'])
 assert scan['output_sha256']==sha(E/'NFN_LOADED_scan.jsonl')
 for x in map(json.loads,(E/'NFN_LOADED_scan.jsonl').read_text().splitlines()):
  assert x['imports_match'] and not x['dangling'] and not x['duplicate_owners']
 # Both top geometry theorems and all L077 roots must be raw-walked in this import.
 roots=set(obj(E/'NFN_AUDIT_ROOTS.json'));assert {r['root'] for r in audit['results']}==roots
 assert {'NFN_NFB_GeometryComposed.result_state_effects','NFN_NFB_GeometryComposed.accepted_physical','AspisR1.RPx_Deployed.deployed'}<=roots
 std={'propext','Classical.choice','Quot.sound'}
 for x in audit['results']:
  assert x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<=std
  assert sha(E/x['graph_archive'])==x['archive_sha256']
 assert len(audit['fixtures'])==8 and all(x['equal'] for x in audit['fixtures'])
 assert all(len(x['walked_axioms'])==1 for x in audit['fixtures'][:4]) and all(not x['walked_axioms'] for x in audit['fixtures'][4:])
 for script in ['NFN_generate.py','NFN_extract_retarget.py']:
  subprocess.run([sys.executable,str(E/script),'--check'],check=True,stdout=subprocess.DEVNULL)
 # Every reused source is pinned to the immutable pre-job revision, never a live sibling.
 pins=obj(E/'NFN_ORIGINAL_SOURCE_PINS.json');graph=obj(E/'NFN_SOURCE_GRAPH.json')
 for x in pins['files']:
  assert hashlib.sha256(graph[x['module']]['source'].encode()).hexdigest()==x['sha256']
  original=subprocess.check_output(['git','show',pins['revision']+':'+x['path']],cwd=R)
  assert hashlib.sha256(original).hexdigest()==x['sha256']
 for name in ['NFN_CANONICAL_IMPORTS.json','NFN_CANONICAL_NATIVE_REUSE.json']:
  assert all(x['import_erased_equal'] for x in obj(E/name))
 # Require current-source successful receipts, not any earlier green draft.
 latest={}
 for line in (E/'NFN_ATTEMPTS.jsonl').read_text().splitlines():
  r=json.loads(line)
  if r['kind']=='lean':latest[r['module']]=r
 for m in ['NFN_PhaseTransport','NFN_ReserveOwner','NFN_ExtractedGeometry']+[f'NFN_GeometryPart{i:02}' for i in range(9)]+['NFN_COMBINED_IMPORT','NFN_ProofDriver']:
  r=latest[m];assert r['exit_status']==0
  assert r['source_hashes']['NFN_generated/'+m+'.lean']==sha(E/(m+'.lean'))
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  ad=obj(E/(r['attempt']+'-admission.json'));assert ad.get('exit',ad.get('exit_status'))==0 and ad['reservation']['allowed'] is True
  assert all('sorryAx' not in x and '_native.decide.ax_' not in x for x in r['print_axioms'])
 return audit

def expected(old,audit):
 return dict(schema='NFN-additive-coherent-geometry-v1',validator_sha256=sha(E/'NFN_validate.py'),baseline_validator_sha256=sha(O/'NFG_validate.py'),baseline_delta_sha256=sha(O/'NFG_LEDGER_DELTA.json'),
  promotions=[dict(row=r,function=ROOT,before='QUALIFIED',after='CLOSED',model=['NFN_NFB_GeometryComposed.result_state_effects','NFN_NFB_GeometryComposed.accepted_physical'],native_packet_sha256=sha(E.parent/'slice-q-compose5-20261104/NFB_GEOMETRY_PACKET.json'),remaining_inner_hypotheses=[]) for r in ROWS],
  newly_coherent_closed=ROWS,newly_counted_source_rows=[],new_count=2,total_closed=old['total_closed'],q_functions_closed=old['q_functions_closed'],q_occurrences_closed=old['q_occurrences_closed'],edge_closed=old['edge_closed'],edge_total=old['edge_total'],
  explanation='The source-only NFB/NFG counts already include these two rows. This removes their joint-headline qualification; it does not count them twice or change an edge.',roots={**old['roots'],ROOT:'CLOSED'},
  audit_sha256=sha(E/'NFN_AUDIT.json'),retarget_provenance_sha256=sha(E/'NFN_RETARGET_PROVENANCE.json'),emitted_retarget_sha256=sha(E/'NFN_EXTRACTED_RETARGET.json'),
  trust=old['trust'],retained=['RootPacketDomain','RootPhysicalInterpretation','NativeContractSemanticTransport','Allocator','frozen3','RuntimePersistence','L154 statement parameter','narrowed D188'],transport='P6/D188 option A reclassification, never removal',cold_release_replay=False,security_target_established=False)

def validate(audit=None,delta=None):
 old=prior.validate(replay=False);assert old==obj(O/'NFG_LEDGER_DELTA.json'),'unchanged NFG validator drift'
 a=own_checks(audit);wanted=expected(old,a)
 delta=obj(E/'NFN_LEDGER_DELTA.json') if delta is None else delta
 assert delta==wanted,'unregistered promotion, source count inflation or hidden change'
 return wanted
if __name__=='__main__':
 start=time.monotonic()
 if '--write' in sys.argv:
  old=prior.validate(replay=False);a=own_checks();result=expected(old,a);(E/'NFN_LEDGER_DELTA.json').write_text(json.dumps(result,indent=1)+'\n')
 else:result=validate()
 print(json.dumps(result))
 usage=resource.getrusage(resource.RUSAGE_SELF)
 (E/'NFN_VALIDATION_RECEIPT.json').write_text(json.dumps(dict(command=sys.argv,exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss,swaps=usage.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),print_axioms='N/A: additive source/evidence validator; Lean audits are pinned separately'),indent=1)+'\n')
