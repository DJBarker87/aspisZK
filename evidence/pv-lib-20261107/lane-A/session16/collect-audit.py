"""Collect the single final strict audit; never launch or repeat it."""
from pathlib import Path
import hashlib,json,lzma,subprocess,shlex
E=Path(__file__).parent;H='/home/dombarker/project-offloads/codex-pv-lib-20261107/lane-A';a=55692
expected=json.loads((E/'AUDIT_ROOTS.json').read_text())['roots'];out=(E/f'out-{a}.log').read_text()
results=[json.loads(l.split('NEP62_RESULT ',1)[1]) for l in out.splitlines() if l.startswith('NEP62_RESULT ')]
assert len(results)==len(expected) and {r['root'] for r in results}==set(expected)
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in results)
mismatches=[r['root'] for r in results if not r['equal']]
assert mismatches==[]
receipt=json.loads((E/f'receipt-{a}.json').read_text());assert receipt['accepted'] and receipt['exit']=='0'
(E/'RAW_AUDIT.json').write_text(json.dumps(dict(attempt=a,strict_raw=True,root_count=len(results),unresolved=0,summary_mismatches=len(mismatches),strict_pass=True,roots=results,receipt=receipt),indent=2)+'\n')
code='''import pathlib,hashlib,json,lzma
p=pathlib.Path(%r)/'evidence/raw-audit';roots=%r
files=[q for q in p.iterdir() if q.is_file() and any(q.name.startswith('NEP_pv-thread_'+r+'_') for r in roots)]
manifest=[dict(name=q.name,bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()) for q in files]
raw=json.dumps({q.name:q.read_text() for q in files if q.suffix in ['.txt','.json']},sort_keys=True).encode()
dest=p.parent/'RAW_GRAPH_ARCHIVE_S16_FINAL.json.xz';dest.write_bytes(lzma.compress(raw))
print(json.dumps(dict(files=manifest,archive_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),archive_bytes=dest.stat().st_size)))'''%(H,expected)
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True);assert r.returncode==0,r.stderr
manifest=json.loads(r.stdout);(E/'RAW_GRAPH_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
subprocess.run(['scp','dombarker@100.108.41.90:'+H+'/evidence/RAW_GRAPH_ARCHIVE_S16_FINAL.json.xz',str(E/'RAW_GRAPH_ARCHIVE.json.xz')],check=True)
assert hashlib.sha256((E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes()).hexdigest()==manifest['archive_sha256']
(E/'RAW_GRAPH_ARCHIVE.json.sha256').write_text(manifest['uncompressed_sha256']+'\n')
print(len(results),'NEW strict roots PASS')
