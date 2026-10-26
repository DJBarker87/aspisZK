"""Validate audit bookkeeping. No prover, compiler, or release gate is invoked."""
from pathlib import Path
from collections import Counter
import json,re,hashlib,subprocess
P=Path(__file__).resolve().parent;ROOT=P.parents[1]
rows=json.loads((P/'premises.json').read_text());counts=json.loads((P/'counts.json').read_text());doc=(ROOT/'design/PRIVACY-LEDGER-20261026.md').read_text()
assert [r['id'] for r in rows]==[f'V{i:03}' for i in range(1,len(rows)+1)]
assert all(r['classification'] in {'T','P','C'} and r['owner'] in {'stream B','external'} for r in rows)
assert all(v==1 for v in Counter(re.findall(r'^\| (V\d+) /',doc,re.M)).values())
assert set(re.findall(r'^\| (V\d+) /',doc,re.M))=={r['id'] for r in rows}
assert all(r['classification']=='T' for r in rows if r['owner']=='external')
assert counts['All syntactic rows']['rows']==len(rows)
for r in rows:
 for file in r['evidence'].split('; '):assert (P/file).exists(),(r['id'],file)
for r in json.loads((P/'source-index.json').read_text()):assert hashlib.sha256((P/r['snapshot']).read_bytes()).hexdigest()==r['sha256']
assert all(r['equal'] for r in json.loads((P/'source-host-comparison.json').read_text()))
receipts=json.loads((P/'receipts.json').read_text());assert sum(r['compiler_invoked'] for r in receipts)==5
for r in receipts:
 assert hashlib.sha256((P/r['module']).read_bytes()).hexdigest()==r['source_sha256']
 for line in r['print_axioms']:
  m=re.search(r'\[([^\]]*)\]',line)
  if m:assert set(x.strip() for x in m[1].split(','))<= {'propext','Classical.choice','Quot.sound'}
 assert (P/r['evidence']).exists()
 if r['compiler_invoked']:
  expected=[line for line in (P/r['evidence']).read_text().splitlines() if re.search(r': error(?:\(|:)',line)]
  assert r['errors']==expected
  if r['exit_status']=='0':assert not expected
assert any('privacy_headline_deployed' in line for r in receipts if r['attempt']==20005 for line in r['print_axioms'])
assert sum(r['status']=='overlap' for r in rows)==57
assert sum(r['group']=='O' for r in rows)==99
assert sum('ALSO one of rw14 remaining35' in r['meaning'] for r in rows)==35
assert sum(r['name'].startswith('L2 F') for r in rows)==14
for p in P.glob('*.lean'):
 assert p.name.startswith('PV_Ledger_')
 assert not re.search(r'^\s*(theorem|lemma|def|axiom|instance|example)\b',p.read_text(),re.M)
assert not any(p.suffix in {'.olean','.elf','.tar','.gz'} for p in P.rglob('*'))
changed=subprocess.check_output(['git','diff','--name-only',json.loads((P/'input-pins.json').read_text())['revision']],cwd=ROOT,text=True).splitlines()
assert all(f.startswith('evidence/privacy-ledger-20261026/') or f=='design/PRIVACY-LEDGER-20261026.md' for f in changed)
assert 'Pending ' not in doc
summary={'validation':'PASS: audit bookkeeping only','rows':len(rows),'counts':counts,'Lean_compiler_invocations':5,'Lean_budget':15,'launcher_only_refusals':1,'Kani':0,'new_proofs':0,'new_theorems':0,'premises_removed':0,'axioms':'all captured existing theorem reports use subsets of propext, Classical.choice, Quot.sound','full_manifest_replay':False,'source_host_comparison':'all retained input-revision source snapshots match post-run host source hashes','limitations':['post-run cached dependency pins are not launch-time coherence or full dependency replay','C rows are vacuity-suspect/inadmissible-route diagnoses, no new checked contradiction','candidate selector tables come from different pinned branches; union unproved']}
(P/'validation-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
