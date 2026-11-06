"""Final local evidence validation; no theorem or native replay."""
from pathlib import Path
import json,lzma,hashlib,subprocess,collections
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):return p.read_bytes()if p.is_file()else lzma.decompress(Path(str(p)+'.xz').read_bytes())
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else raw(p))
large=[str(p)for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000];assert not large,large
compressed=[]
for p in E.rglob('*.sha256'):
 z=Path(str(p)[:-7]+'.xz')
 if not z.is_file():continue
 expected=p.read_text().strip().split()[0];assert H(lzma.decompress(z.read_bytes()))==expected,str(z);compressed.append(str(z))
audit=J(E/'NLO_AUDIT.json');assert audit['full_composition_pass']and audit['required_roots']==11174
ledger=J(E/'NLO_LEDGER.json.xz');basis=J(E.parent/'ledger21-20261110/NLG_LEDGER.json.xz');delta=J(E/'NLO_LEDGER_DELTA.json');assert len(ledger['rows'])==599 and ledger['trust_rows']==basis['trust_rows']and len(delta['rows'])==12
assert collections.Counter(r['status']for r in ledger['rows'])=={'CLOSED':576,'OPEN':23}
assert [r['canonical_callees']for r in ledger['rows']]==[r['canonical_callees']for r in basis['rows']]
statements=J(E/'NLO_KERNEL_STATEMENTS.json.xz');refs=[]
for r in ledger['rows']:
 assert H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())==r['obligation_statement_hash'],r['row']
 for x in r.get('root_owners',[]):
  assert x['root']in statements and statements[x['root']]['owner_module']==x['owner_module']
  if 'obligation_statement_sha256'in x:assert H(statements[x['root']]['obligation_statement'].encode())==x['obligation_statement_sha256']
  refs.append(x)
closure=J(E/'NLO_CLOSURE_PINS.json.xz');selected={Path(r['path']).name:r for r in closure['selected_objects']};support=[]
for seed in J(E.parent/'batch-merkle6-20261110/NLN_SEEDS.json'):
 if seed['seed'] not in ['NLL','NKV']:continue
 for f in seed['files']:
  item=dict(provider=seed['seed'],export=seed['source'],relative=f['path'],expected_sha256=f['sha256'])
  actual=selected.get(Path(f['path']).name)
  if actual:assert actual['sha256']==f['sha256'];item.update(selected=actual,status='IMPORTED_HASH_MATCH')
  else:item.update(status='UNUSED_EXPORT_NOT_CREDITED')
  support.append(item)
(E/'NLO_SUPPORT_EXPORT_REVIEW.json').write_text(json.dumps(dict(status='PASS',files=support),indent=1)+'\n')
rcs=[]
for line in(E/'NLO_ATTEMPTS.jsonl').read_text().splitlines():
 row=json.loads(line);r=J(E/row['attempt']/'receipt.json')
 assert r['source_revision'] and r['command'] and r['peak_rss_kib']and r['swaps']=='0'
 for n,h in r['source_hashes'].items():assert H(raw(E/row['attempt']/'sources'/n))==h,(row['attempt'],n)
 rcs.append(r)
assert len(rcs)==40
assert not(E/'NLO_CLIENT_ACTIVE').exists()
changed=subprocess.check_output(['git','diff','--name-only','17dc0c0d963'],text=True).splitlines();assert all(n.startswith('evidence/ledger22-20261110/')for n in changed),changed
out=dict(status='PASS',files_under20MB=True,compressed_sha_pairs=len(compressed),scope_receipts=40,root_owner_references=len(refs),changed_paths_only_own_evidence=True,shipped_source_unchanged=True,trust_rows_unchanged=True,all_edges_retained=True,candidate_count=12,target_established=False)
(E/'NLO_INTEGRITY.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
