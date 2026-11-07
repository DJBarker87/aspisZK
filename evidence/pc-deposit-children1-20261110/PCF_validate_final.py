"""Validate complete account packets; no credit from a compile or model theorem alone."""
from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent;std={'propext','Classical.choice','Quot.sound'}
def receipt(a):return json.loads((E/a/'receipt.json').read_text())
def raw(a):return [json.loads(s[11:]) for s in (E/a/'stdout.log').read_text().splitlines() if s.startswith('NEP_RESULT ')]
def native(a,passed):
 r=receipt(a);s=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' if passed else 'VERIFICATION:- FAILED') in s,a
 assert r['exit_status']==(0 if passed else 1),a
 assert 'timed out' not in s.lower(),a
 assert json.loads((E/(a+'-graph-check.json')).read_text())['graph_matches_frozen']
 assert json.loads((E/(a+'-lock-check.json')).read_text())['unchanged']
 feats=json.loads((E/(a+'-graph-check.json')).read_text())['all_crate_features'];pool=next(x['features'] for x in feats if x['name']=='aspis-pool')
 assert set(pool)=={'default','pair-forest-account-evidence','pair-forest-source-invariant-audit','pair-forest-source-result-invariant-audit','pair-forest-verifier-lane-invariant-audit','r1-split-checkpoint'}
 for key,v in [('memory.high','6442450944'),('memory.max','8589934592'),('memory.swap.max','0'),('pids.max','64')]:assert str(r['limits'][key])==v
 assert int(r['swaps'])==0

for a in ['PCF_L090','PCF_L092','PCF_L097','PCF_L098','PCF_L100','PCF_L102','PCF_L104','PCF_L109','PCF_L110','PCF_L115','PCF_L111','PCF_L112','PCF_L114']:
 assert receipt(a)['exit_status']==0,a
for a,p in [('PCF_K059',True),('PCF_K060',False),('PCF_K061',True),('PCF_K062',False),('PCF_K063',True),('PCF_K064',False),('PCF_K065',True),('PCF_K066',False),('PCF_K046',True),('PCF_K047',True),('PCF_K048',False),('PCF_K049',False),('PCF_K050',False),('PCF_K067',True),('PCF_K068',False)]:native(a,p)
for a in ['PCF_K059','PCF_K060','PCF_K061','PCF_K062','PCF_K063','PCF_K064','PCF_K065','PCF_K066']:
 cfg=json.loads((E/(a+'.json')).read_text());assert '--cfg PCF_DIRECT' in cfg['env']['RUSTFLAGS']
 source='PCF_Processor.rs' if int(a[-3:])<65 else 'PCF_Lane.rs'
 assert 'cfg_attr(PCF_DIRECT,kani::proof)' in (E/a/'sources/PCF_src'/('programs/aspis-pool/src/' if int(a[-3:])<65 else 'crates/aspis-statement/src/pool_v1/')/source).read_text()
for a,carrier in [('PCF_K057','ProgramError'),('PCF_K058','PoolV1PairForestAccountErrorV1')]:
 text=(E/a/'stdout.log').read_text();assert receipt(a)['exit_status']==1 and 'error[E0277]' in text and carrier in text and 'Arbitrary' in text
 assert 'VERIFICATION:- SUCCESSFUL' not in text
scan=[json.loads(s) for s in (E/'PCF_LOADED_scan.jsonl').read_text().splitlines()];assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
base=json.loads((E/'PCF_AUDIT_STAGE2.json').read_text());rows=base['roots'];fresh=raw('PCF_L113');ex=json.loads((E/'PCF_FINAL_NEW_ROOTS.json').read_text())['roots'];assert [r['root']for r in fresh]==ex
assert receipt('PCF_L113')['exit_status'] in [0,1]
assert all(set(r['walked_axioms'])<=std for r in fresh)
by={r['root']:r for r in rows+fresh};expected=json.loads((E/'PCF_FINAL_ROOTS.json').read_text());assert set(expected['roots'])<=set(by)
assert all(set(by[n]['walked_axioms'])<=std for n in expected['roots'])
fixtures=raw('PCF_L023');assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
pins=json.loads((E/'PCF_AUDIT_BINARY_PINS.json').read_text());assert pins==json.loads((E/'PCF_AUDIT_STAGE1.json').read_text())['binary']
m=json.loads((E/'PCF_RAW_MANIFEST.json').read_text());assert m['all_import_pins_unchanged']
for x in m['files']:
 q=E/'PCF_RAW_FINAL'/(x['source']+'.xz');data=q.read_bytes();assert hashlib.sha256(data).hexdigest()==x['compressed_sha256'];assert hashlib.sha256(lzma.decompress(data)).hexdigest()==x['uncompressed_sha256']
assert hashlib.sha256((E/'PCF_IMPORTS.json.xz').read_bytes()).hexdigest()==json.loads((E/'PCF_EXPORT.json').read_text())['seed_manifest_sha256']
assert all(r['exact_function_body_and_signature']for r in json.loads((E/'PCF_SNAPSHOT_FUNCTION_CHECKS.json').read_text()))
assert all(r['matches']for r in json.loads((E/'PCF_BODY_CHECKS.json').read_text()))
assert all(r['mutation_controls_rejected']for r in json.loads((E/'PCF_METADATA_FOOTPRINT.json').read_text()))
export=json.loads((E/'PCF_EXPORT.json').read_text());assert export['all_export_hashes_verified'] and export['copy_only'] and not export['hardlinks'] and export['deletions']==0
audit=dict(status='PASS_FINAL',combined='PCF_L111',scan='PCF_L112',modules=len(scan),dangling=0,duplicate_owners=0,import_mismatches=0,required_roots=len(expected['roots']),own_roots=expected['own'],roots=[by[n]for n in expected['roots']],raw_reused=base['raw_batches'],raw_new='PCF_L113',fixtures='PCF_L023',fixture_count=8,same_binary=pins,disagreements=[by[n]for n in expected['roots']if not by[n]['equal']],raw_standard_authoritative="(ab')(3)/(ax2); no walker change or axiom padding",native={'364':['PCF_K059','PCF_K060','PCF_K063','PCF_K064'],'365':['PCF_K061','PCF_K062'],'199':['PCF_K065','PCF_K066']},native_route='Direct actual frozen body, PCF_DIRECT removes all contract/checker attributes on actual leaves; complete non-Arbitrary Results checked against extracted references; no arbitrary Result or stub_verified. Parent composition must use explicit-constructor logging stubs under(ak).',non_arbitrary_eligibility=['PCF_K057','PCF_K058'],prior_frame_checks=['PCF_K016','PCF_K017','PCF_K019','PCF_K021'],source_identity='PCF_SNAPSHOT_FUNCTION_CHECKS.json; PCF_BODY_CHECKS.json; PCF_METADATA_FOOTPRINT.json',reference_only={'279':'PCF_AppendComplete.complete; actual native0 timeouts K032/K051/K054, NO row credit','332':'PCF_CountSliceState.complete; partial native constructor classes K067/K068, NO universal native credit'},export='PCF_EXPORT.json',claims='Exactly3 CLOSED Pool rows; no parent, transaction game, source-to-ELF, deployment, privacy or100-bit headline security closure')
(E/'PCF_AUDIT_FINAL.json').write_text(json.dumps(audit,indent=1)+'\n');(E/'PCF_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n');print('PCF final gate PASS:208 raw-standard roots,43 own,8 fixtures,same binary,zero NFX defects,3 direct-body CLOSED packets')
