"""Archive/source/quotation checks; no prover rerun and no excluded input."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();checks=[]
for p in E.rglob('*.sha256'):
 base=Path(str(p).removesuffix('.sha256'));q=Path(str(base)+'.xz');q=q if q.is_file()else base
 if q.is_file():
  b=lzma.decompress(q.read_bytes())if q.suffix=='.xz'else q.read_bytes();assert H(b)==p.read_text().strip(),str(p);checks.append(str(p.relative_to(E)))
refs=[]
for p in E.rglob('*.REFERENCE.json'):
 x=json.loads(p.read_text());q=E/x['stored_once'];b=lzma.decompress(q.read_bytes())if x['encoding']=='xz'else q.read_bytes();assert H(b)==x['sha256']and len(b)==x['bytes'];refs.append(str(p.relative_to(E)))
required=['NHO_LEDGER.md','NHO_LEDGER.json.xz','NHO_ROUTES.json','NHO_TRUST_USED.json','NHO_COMBINED_IMPORT.lean','NHO_AUDIT.json','NHO_SCAN.json','NHO_CONFLICTS.json','NHO_STATEMENT.md','NHO_SHORTEST_PATHS.md','NHO_HANDOFF.md','NHO_REMAINING.md','NHO_ATTEMPTS.jsonl']
assert all((E/n).is_file()for n in required)
quotes=json.loads((E/'NHO_STATEMENT_QUOTES.json').read_text());text=(E/'NHO_STATEMENTS.md').read_text()
for x in quotes:assert x['name']in text and x['axiom_line']in text
assert len(quotes)==5 and'Target not yet established'in(E/'NHO_STATEMENT.md').read_text()
for p in E.rglob('*'):
 assert p.name!='__pycache__'
 if p.is_file():
  assert p.stat().st_size<=20_000_000,str(p)
  assert not p.name.endswith(('.olean','.ir','.o','.so','.a','.tar','.tgz','.elf','.pyc')),str(p)
result=dict(status='PASS',archive_sha_checks=len(checks),content_addressed_references=len(refs),required_outputs=required,full_statements=len(quotes),no_oversize_file=True,no_binaries_objects_or_bytecode=True)
(E/'NHO_ARTIFACTS.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
