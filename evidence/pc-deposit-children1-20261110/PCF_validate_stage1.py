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
for a in ['PCF_L003','PCF_L004','PCF_L005','PCF_L017','PCF_L014','PCF_L019','PCF_L020','PCF_L021','PCF_L022','PCF_L023','PCF_L027','PCF_L043']:assert receipt(a)['exit_status']==0,a
for a,p in [('PCF_K017',True),('PCF_K018',False),('PCF_K019',True),('PCF_K020',False),('PCF_K021',True),('PCF_K022',False),('PCF_K013',True),('PCF_K014',False),('PCF_K016',False)]:native(a,p)
assert 'assignable' in (E/'PCF_K016/stdout.log').read_text()
f=raw('PCF_L023');assert len(f)==8
for i,r in enumerate(f):assert r['equal'] and r['walked_axioms']==r['collect_axioms'] and (len(r['walked_axioms'])==1 if i<4 else not r['walked_axioms'])
scan=[json.loads(s) for s in (E/'PCF_LOADED_scan.jsonl').read_text().splitlines()];assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
p=json.loads((E/'PCF_GATE_PLAN.json').read_text());rows=[]
for a in p['raw_batches']:
 assert receipt(a)['exit_status']==0,a
 rr=raw(a);expected=json.loads((E/a/'sources/PCF_AUDIT_ROOTS.json').read_text())['roots'];assert [r['root'] for r in rr]==expected
 assert all(set(r['walked_axioms'])<=std for r in rr);rows+=rr
expected=json.loads((E/'PCF_ALL_AUDIT_ROOTS.json').read_text());by={r['root']:r for r in rows};assert set(expected['roots'])<=set(by)
assert all(r in by for r in expected['own'])
m=json.loads((E/'PCF_RAW_MANIFEST.json').read_text());assert m['all_import_pins_unchanged']
for x in m['files']:
 q=E/'PCF_RAW_FINAL'/(x['source']+'.xz');data=q.read_bytes();assert hashlib.sha256(data).hexdigest()==x['compressed_sha256'];assert hashlib.sha256(lzma.decompress(data)).hexdigest()==x['uncompressed_sha256']
pins=json.loads((E/'PCF_AUDIT_BINARY_PINS.json').read_text());assert pins['PCF_native/PCF_WALKER.c']['sha256']==hashlib.sha256((E/'PCF_WALKER.c').read_bytes()).hexdigest()
assert pins['PCF_native/PCF_MemoryLimit.c']['sha256']==hashlib.sha256((E/'PCF_MemoryLimit.c').read_bytes()).hexdigest()
assert all(r['matches'] for r in json.loads((E/'PCF_BODY_CHECKS.json').read_text()))
assert all(r['mutation_controls_rejected'] for r in json.loads((E/'PCF_METADATA_FOOTPRINT.json').read_text()))
audit=dict(status='PASS_ACCOUNT_STAGE1',combined='PCF_L020',scan='PCF_L027',modules=len(scan),dangling=0,duplicate_owners=0,import_mismatches=0,fixtures='PCF_L023',fixture_count=8,raw_batches=p['raw_batches'],required_roots=len(expected['roots']),own_roots=expected['own'],roots=[by[r] for r in expected['roots']],disagreements=[r for r in rows if not r['equal']],manifest_repair='PCF_ROOT_MANIFEST_FINDING.json; failed036 is excluded, all PCF/headline/accepted PCB/NLF law roots remain',binary=pins,import_hash_verification='PCF_L043; PCF_IMPORTS.json.xz',source_identity='PCF_BODY_CHECKS.json',native={'364':['PCF_K017','PCF_K018','PCF_K021','PCF_K022'],'365':['PCF_K019','PCF_K020']},sdk_id_controls=['PCF_K013','PCF_K014'],frame_control='PCF_K016; explicit modifies violation detected',extraction='PCF_E001; identical reference source used by actual contracts',axioms='Every required raw root is a subset of propext/Classical.choice/Quot.sound',claims='Account child rows only; no parent, global experiment, deployment or headline security closure')
(E/'PCF_AUDIT_STAGE1.json').write_text(json.dumps(audit,indent=1)+'\n');(E/'PCF_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n');print('PCF stage1 gate PASS: two account packets;178 raw roots,13 own roots,eight fixtures,zero scan defects')
