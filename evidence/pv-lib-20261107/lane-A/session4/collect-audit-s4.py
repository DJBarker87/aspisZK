"""Collect exactly one successful raw audit, never launch or repeat it."""
from pathlib import Path
import hashlib,json,lzma,subprocess,shlex
E=Path('evidence/pv-lib-20261107/lane-A/session4');H='/home/dombarker/project-offloads/codex-pv-lib-20261107/lane-A';a=49890
expected=json.load(open(E/'AUDIT_ROOTS.json'))['roots'];out=(E/f'out-{a}.log').read_text()
results=[json.loads(l.split('NEP62_RESULT ',1)[1]) for l in out.splitlines() if l.startswith('NEP62_RESULT ')]
assert len(results)==len(expected) and {r['root'] for r in results}==set(expected)
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in results)
receipt=json.load(open(E/f'receipt-{a}.json'));assert receipt['accepted']
(E/'RAW_AUDIT.json').write_text(json.dumps(dict(attempt=a,strict_raw=True,root_count=len(results),unresolved=0,summary_mismatches=0,roots=results,receipt=receipt),indent=2)+'\n')
code='''import pathlib,hashlib,json,lzma
p=pathlib.Path(%r)/'evidence/raw-audit';roots=%r
files=[q for q in p.iterdir() if q.is_file() and any(q.name.startswith('NEP_pv-thread_'+r+'_') for r in roots)]
manifest=[dict(name=q.name,bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()) for q in files]
raw=json.dumps({q.name:q.read_text() for q in files if q.suffix in ['.txt','.json']},sort_keys=True).encode()
dest=p.parent/'RAW_GRAPH_ARCHIVE_S4.json.xz';dest.write_bytes(lzma.compress(raw))
print(json.dumps(dict(files=manifest,archive_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),archive_bytes=dest.stat().st_size)))'''%(H,expected)
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True);assert r.returncode==0,r.stderr
manifest=json.loads(r.stdout);(E/'RAW_GRAPH_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
subprocess.run(['scp','dombarker@100.108.41.90:'+H+'/evidence/RAW_GRAPH_ARCHIVE_S4.json.xz',str(E/'RAW_GRAPH_ARCHIVE.json.xz')],check=True)
assert hashlib.sha256((E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes()).hexdigest()==manifest['archive_sha256']
(E/'RAW_GRAPH_ARCHIVE.json.sha256').write_text(manifest['uncompressed_sha256']+'\n')
print(len(results),'strict roots passed')
