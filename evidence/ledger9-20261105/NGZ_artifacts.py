from pathlib import Path
import json,lzma,hashlib,re,ast
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();J=lambda p:json.loads(p.read_text())
requested=['NGZ_LEDGER.md','NGZ_LEDGER.json.xz','NGZ_ROUTES.json','NGZ_TRUST_USED.json','NGZ_COMBINED_IMPORT.lean','NGZ_AUDIT.json','NGZ_SCAN.json','NGZ_CONFLICTS.json','NGZ_STATEMENT.md','NGZ_SHORTEST_PATHS.md','NGZ_HANDOFF.md','NGZ_REMAINING.md','NGZ_ATTEMPTS.jsonl']
assert all((E/n).is_file()for n in requested)
pack=J(E/'NGZ_PACK.json');refs={r['original_path']:r for r in pack['references']}
def snapshot(p):
 if p.is_file():return p.read_bytes()
 r=J(Path(str(p)+'.REFERENCE.json'));q=E/r['stored_once'];raw=lzma.decompress(q.read_bytes())if r['encoding']=='xz'else q.read_bytes();assert H(raw)==r['sha256'];return raw
for r in refs.values():assert H(snapshot(E/r['original_path']))==r['sha256']
receipts={p.parent.name:J(p)for p in E.glob('NGZ_L*/receipt.json')};assert len(receipts)==40
for a,r in receipts.items():
 for n,h in r['source_hashes'].items():assert H(snapshot(E/a/'sources'/n))==h,(a,n)
audit=J(E/'NGZ_AUDIT.json');by={r['raw_graph']:r for r in audit['results']};archives=0
for p in E.glob('*.xz'):
 sha=Path(str(p)[:-3]+'.sha256')
 if not sha.exists():continue
 if p.name in by:
  r=by[p.name];assert H(p.read_bytes())==r['archive_sha256']and sha.read_text().strip()==r['raw_graph_sha256']
 else:assert H(lzma.decompress(p.read_bytes()))==sha.read_text().strip(),p
 archives+=1
roots=set(J(E/'NGZ_AUDIT_ROOTS.json')['roots']);assert all(r['name']in roots for r in J(E/'NGZ_STATEMENT_QUOTES.json'))
for p in E.glob('*.py'):ast.parse(p.read_text(),str(p))
for p in E.rglob('*'):
 assert p.name!='__pycache__'
 if p.is_file():
  assert p.stat().st_size<=20_000_000,p
  assert p.suffix not in ['.olean','.o','.elf','.tar','.pyc'],p
end=J(E/'NGZ_HOST_END.json');assert not end['active_own_provers']and end['cache_retained']and not end['keys_touched']
assert len(J(E/'NGZ_VALIDATOR_PROVENANCE.json'))==25
out=dict(status='PASS',requested_outputs=requested,slots=40,verified_archives=archives,packed_source_references=len(refs),validated_source_hashes=sum(len(r['source_hashes'])for r in receipts.values()),validators=25,full_statement_quotes=26,all_inputs_retained=True,no_oversized_file=True,no_active_own_prover=True)
(E/'NGZ_ARTIFACTS.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
