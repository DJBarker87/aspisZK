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

plan=json.loads((E/'PCF_STAGE2_PLAN.json').read_text())
for a in ['PCF_L057','PCF_L054','PCF_L063',plan['combined'],plan['scan'],'PCF_L077']:
 assert receipt(a)['exit_status']==0,a
native('PCF_K009',True);native('PCF_K010',False)
scan=[json.loads(s) for s in (E/'PCF_LOADED_scan.jsonl').read_text().splitlines()]
assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
rows=[]
for a in plan['raw_batches']:
 assert receipt(a)['exit_status']==0,a
 rr=raw(a);ex=json.loads((E/a/'sources/PCF_AUDIT_ROOTS.json').read_text())['roots']
 assert [r['root'] for r in rr]==ex
 assert all(set(r['walked_axioms'])<=std for r in rr)
 rows+=rr
expected=json.loads((E/'PCF_STAGE2_ROOTS.json').read_text());assert [r['root'] for r in rows]==expected['roots']
fixtures=raw('PCF_L023');assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
pins=json.loads((E/'PCF_AUDIT_BINARY_PINS.json').read_text());oldpins=json.loads((E/'PCF_AUDIT_STAGE1.json').read_text())['binary']
assert pins==oldpins, 'same binary required'
m=json.loads((E/'PCF_RAW_MANIFEST.json').read_text());assert m['all_import_pins_unchanged']
for x in m['files']:
 q=E/'PCF_RAW_FINAL'/(x['source']+'.xz');data=q.read_bytes();assert hashlib.sha256(data).hexdigest()==x['compressed_sha256'];assert hashlib.sha256(lzma.decompress(data)).hexdigest()==x['uncompressed_sha256']
audit=dict(status='PASS_STAGE2',combined=plan['combined'],scan=plan['scan'],modules=len(scan),dangling=0,duplicate_owners=0,import_mismatches=0,fixtures='PCF_L023',fixture_count=8,same_binary=pins,required_roots=len(rows),own_roots=expected['own'],roots=rows,raw_batches=plan['raw_batches'],disagreements=[r for r in rows if not r['equal']],native={'199':['PCF_K009','PCF_K010']},extraction='PCF_E002',lean='PCF_L063',axioms='All192 required raw sets are standard',claims='One additional child199; no parent or headline security closure')
(E/'PCF_AUDIT_STAGE2.json').write_text(json.dumps(audit,indent=1)+'\n');(E/'PCF_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n');print('PCF stage2 PASS: lane199,192 raw roots,eight fixtures,same binary,zero scan defects')
