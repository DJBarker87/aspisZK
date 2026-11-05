"""Final file/hash/closure/source-snapshot checks; no formal invocation."""
from pathlib import Path
import json,lzma,hashlib,ast
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();checks=0
required=['NII_LEDGER.md','NII_LEDGER.json','NII_ROUTES.json','NII_TRUST_USED.json','NII_COMBINED_IMPORT.lean','NII_AUDIT.json','NII_SCAN.json','NII_CONFLICTS.json','NII_STATEMENT.md','NII_SHORTEST_PATHS.md','NII_HANDOFF.md','NII_REMAINING.md','NII_ATTEMPTS.jsonl']
for n in required:assert(E/n).is_file()or(E/(n+'.xz')).is_file(),n
for p in E.rglob('*'):
 assert p.name!='__pycache__'and p.suffix not in ['.pyc','.olean','.ir','.o','.so','.dylib','.a','.bc','.llbc','.elf'],p
 if p.is_file():assert p.stat().st_size<=20_000_000,p
for p in E.rglob('*.sha256'):
 name=str(p).removesuffix('.sha256');archive=Path(name+'.xz')
 if archive.exists():assert H(lzma.decompress(archive.read_bytes()))==p.read_text().strip(),p;checks+=1
for p in E.glob('NII_*.py'):ast.parse(p.read_text(),filename=str(p));checks+=1
pack=json.loads((E/'NII_PACK.json').read_text())
for r in pack['references']:
 raw=(E/r['stored_once']).read_bytes();raw=lzma.decompress(raw)if r['encoding']=='xz'else raw;assert H(raw)==r['sha256']and len(raw)==r['bytes'];assert not(E/r['original_path']).exists();checks+=1
cp=json.loads(lzma.decompress((E/'NII_CLOSURE_PINS.json.xz').read_bytes()));assert cp['full_composition_pass']is False
assert any('/Aeneas/'in r['path']for r in cp['selected_objects'])
exp=json.loads((E/'NII_EXPORT.json').read_text());assert exp['full_import_object_exists']is False and len(exp['files'])==4
conf=json.loads((E/'NII_CONFLICTS.json').read_text())
for o in conf['owners']:assert H((E/o['snapshot']).read_bytes())==o['sha256'];checks+=1
# Snapshot printed kernel statements independently against the stored quotation hashes.
statements=(E/'NII_STATEMENTS.md').read_text();quotes=json.loads((E/'NII_STATEMENT_QUOTES.json').read_text())
for q in quotes:
 section=statements.split('## '+q['name']+'\n\n```lean\n',1)[1].split('\n```',1)[0];assert H(section.encode())==q['quote_sha256'];checks+=1
assert len(quotes)==10
out=dict(status='PASS',required_outputs=len(required),archive_sha_checks=checks,source_references=len(pack['references']),closure_files=len(cp['selected_objects']),own_exports=len(exp['files']),no_large_file_or_binary=True,no_bytecode=True,full_composition_pass=False,all_requested_gate_failures_preserved=True)
(E/'NII_ARTIFACTS.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
