"""Read-only bookkeeping/provenance checks; no formal or runtime gate."""
from pathlib import Path
from collections import Counter
import json,subprocess,re,hashlib
P=Path(__file__).resolve().parent;ROOT=P.parents[1]
def git(*a):return subprocess.check_output(['git',*a],cwd=ROOT)
rows=json.loads((P/'rows.json').read_text());tot=json.loads((P/'totals.json').read_text());pins=json.loads((P/'pins.json').read_text())
assert len(rows)==400 and len({r['id'] for r in rows})==400
assert [r['id'] for r in rows[:-1]]==[f'V{i:03}' for i in range(1,400)]
assert rows[-1]['id']=='V380-inversion' and rows[379]['name']=='TrustedStd.btree_entry_or_insert_with'
base=pins['research']['revision'];old=git('show',base+':design/PRIVACY-LEDGER-20261026.md');new=(ROOT/'design/PRIVACY-LEDGER-20261026.md').read_bytes();assert new.startswith(old)
assert new[len(old):].startswith(b'\n\n## Recount 2026-10-26 (B)')
baseline=json.loads((ROOT/'evidence/privacy-ledger-20261026/premises.json').read_text())
for before,after in zip(baseline,rows):
 for k,v in before.items():assert after[k]==v,(after['id'],k)
assert Counter(r['classification'] for r in rows)=={'T':26,'P':370,'C':4}
assert Counter(r['recount_status'] for r in rows)=={'OPEN':138,'REDUCED':152,'EVIDENCED':10,'CLOSED-ON-RESEARCH':87,'CLOSED-ON-CANDIDATE':13}
assert Counter(r['dependency_bucket'] for r in rows if r['recount_status']=='OPEN')=={'a':79,'b':51,'c':8}
assert all((r['dependency_bucket'] in 'abc') if r['recount_status']=='OPEN' else r['dependency_bucket'] is None for r in rows)
assert all(r['residual_fields'] for r in rows if r['recount_status']=='REDUCED')
assert all(r['theorem'] for r in rows if r['recount_status'].startswith('CLOSED'))
assert all(rows[i-1]['recount_status']=='OPEN' for i in range(347,370))
assert rows[-1]['recount_status']=='OPEN'
# All captured source snapshots are byte-exact pinned git objects, not new Lean modules.
manifest=json.loads((P/'source-manifest.json').read_text());captured=0
for m in manifest:
 if m['exit']:continue
 data=(P/m['local']).read_bytes();assert len(data)==m['bytes'];assert hashlib.sha256(data).hexdigest()==m['sha256'];assert data==git('show',m['revision']+':'+m['path']);captured+=1
assert not list(P.rglob('*.lean'))
for label,pin in pins.items():
 if 'path' in pin:assert (P/(label+'.txt')).read_bytes()==git('show',pin['revision']+':'+pin['path'])
for f in (P/'rebase-evidence').rglob('*.json'):
 path='docs/research/100bit-spend-path-20261013/evidence/pv-rebase-20261026/'+str(f.relative_to(P/'rebase-evidence'))
 assert f.read_bytes()==git('show',pins['rebase']['revision']+':'+path)
for mode in ['default','devnet','pool']:
 c=json.loads((P/f'rebase-evidence/candidate/build-{mode}/comparison.json').read_text());assert c['matches'] and c['sha256']==c['expected']
assert json.loads((P/'rebase-evidence/fixture-comparison.json').read_text())['passed']
receipt=json.loads((P/'inputs/dict/docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/reach7/20701-receipt.json').read_text())
lines=receipt['print_axioms'];assert len(lines)==486
for r in rows:
 if r['recount_status']=='CLOSED-ON-CANDIDATE':
  line=next(x for x in lines if x.startswith("'"+r['theorem']+"' "));assert 'sorryAx' not in line
  if 'depends on axioms:' in line:assert set(re.search(r'\[(.*)\]',line)[1].split(', '))<={'propext','Classical.choice','Quot.sound'}
changed=git('diff','--name-only',base).decode().splitlines()
assert all(f=='design/PRIVACY-LEDGER-20261026.md' or f.startswith('evidence/privacy-recount-20261026/') for f in changed)
result=dict(result='PASS',source_revision=git('rev-parse','HEAD').decode().strip(),baseline_revision=base,original_ledger_sha256=hashlib.sha256(old).hexdigest(),original_ledger_bytes=len(old),original_rows_preserved=399,audit_rows=400,source_objects_checked=captured,candidate_closure_axiom_lines_checked=13,lean_invocations=0,kani_invocations=0,host_runs=0,final_manifest_replay=False,claims='bookkeeping, original preservation and pinned evidence provenance only',totals=tot)
(P/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['result','original_rows_preserved','audit_rows','source_objects_checked','candidate_closure_axiom_lines_checked','lean_invocations','kani_invocations']}))
