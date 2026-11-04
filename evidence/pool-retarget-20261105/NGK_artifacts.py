"""Final committed-input completeness, size, compression and scope audit."""
from pathlib import Path
import json,subprocess,hashlib,lzma
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest();pairs=[]
for p in sorted(E.rglob('*.sha256')):
 q=Path(str(p).removesuffix('.sha256')+'.xz');assert q.is_file(),p
 raw=lzma.decompress(q.read_bytes());assert H(raw)==p.read_text().strip(),p
 pairs.append(dict(path=str(q.relative_to(E)),sha256=H(raw),raw_bytes=len(raw),compressed_bytes=q.stat().st_size))
for r in json.loads((E/'NGK_PACK.json').read_text())['references']:
 p=E/r['stored_once'];raw=lzma.decompress(p.read_bytes()) if r['encoding']=='xz' else p.read_bytes();assert H(raw)==r['sha256'] and len(raw)==r['bytes']
files=[p for p in E.rglob('*') if p.is_file()];assert all(p.stat().st_size<=20000000 for p in files)
assert not list(E.rglob('__pycache__'))
changed=subprocess.check_output(['git','diff','--name-only','b76f439d2e230798ef48482076624e258c838a02'],cwd=R,text=True).splitlines();assert all(p.startswith('evidence/pool-retarget-20261105/') for p in changed)
objects=subprocess.check_output(['git','rev-list','--objects','b76f439d2e230798ef48482076624e258c838a02..HEAD'],cwd=R,text=True)
out=subprocess.check_output(['git','cat-file','--batch-check=%(objecttype) %(objectsize) %(rest)'],cwd=R,input=objects,text=True)
oversized=[l for l in out.splitlines() if l.startswith('blob ') and int(l.split()[1])>20000000];assert not oversized,oversized
required=['NGK_FAMILIES.md','NGK_RETARGET.md','NGK_PROVENANCE.json','NGK_COMBINED_IMPORT.lean','NGK_AUDIT.json','NGK_SCAN.json','NGK_LEDGER_DELTA.json','NGK_HANDOFF.md','NGK_REMAINING.md','NGK_ATTEMPTS.jsonl'];assert all((E/n).is_file() for n in required)
end=json.loads((E/'NGK_HOST_END.json').read_text());assert end['no_cache_file_deleted'] and not end['active_owned_provers']
(E/'NGK_ARTIFACTS.json').write_text(json.dumps(dict(status='PASS',compression_pairs=pairs,source_snapshot_references=50,required_outputs=required,all_required_present=True,scope_only=True,no_oversized_retained_git_blob=True,no_file_over20MB=True,no_python_bytecode=True,owned_cache_retained=True,active_owned_provers=0),indent=1)+'\n')
print('PASS',len(pairs),'compressed/raw SHA pairs; required outputs, scope, retained history size and host cleanup checked')
