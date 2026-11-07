"""Collect one completed strict audit; never relaunch it."""
import hashlib,json,lzma,pathlib,shlex,subprocess
E=pathlib.Path('evidence/pv-lib-20261107/lane-SLICE');H='/home/dombarker/project-offloads/codex-pv-lib-slice-20261107'
expected=json.loads((E/'AUDIT_ROOTS.json').read_text())['roots']
out=(E/'out-49690.log').read_text()
results=[json.loads(line.split('NEP62_RESULT ',1)[1]) for line in out.splitlines() if line.startswith('NEP62_RESULT ')]
assert len(results)==len(expected) and {r['root'] for r in results}==set(expected)
assert all(r['equal'] for r in results)
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in results)
receipt=json.loads((E/'receipt-49690.json').read_text());assert receipt['accepted']
summary=dict(attempt=49690,strict_raw=True,root_count=len(results),unresolved=0,
    summary_mismatches=0,roots=results,receipt=receipt,
    qualification='Unchanged NEP private importAll walker; unresolved is a hard error. Only the new PLIB roots; no frozen-manifest replay.')
(E/'RAW_AUDIT.json').write_text(json.dumps(summary,indent=2)+'\n')
code=r'''
import pathlib,hashlib,json,lzma
p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/evidence/raw-audit')
roots=['PV_LIB_SLICE_BoundedRun.selected', 'PV_LIB_SLICE_BoundedRun.least', 'PV_LIB_SLICE_F32.certified', 'PV_LIB_SLICE_F32.functional', 'PV_LIB_SLICE_F33.certified', 'PV_LIB_SLICE_F33.functional', 'PV_LIB_SLICE_TypedDrop.certified', 'PV_LIB_SLICE_TypedDrop.selected', 'PV_LIB_SLICE_EntryReference.certified', 'PV_LIB_SLICE_EntryReference.old_entry']
files=[q for q in p.iterdir() if q.is_file() and any(q.name.startswith('NEP_pv-thread_'+root+'_') for root in roots)]
manifest=[dict(name=q.name,bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()) for q in files]
payload={q.name:q.read_text() for q in files if q.suffix in ['.txt','.json']}
raw=json.dumps(payload,sort_keys=True).encode()
dest=p.parent/'RAW_GRAPH_ARCHIVE.json.xz';dest.write_bytes(lzma.compress(raw))
print(json.dumps(dict(files=manifest,archive_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),archive_bytes=dest.stat().st_size)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True)
assert r.returncode==0,r.stderr
manifest=json.loads(r.stdout);(E/'RAW_GRAPH_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
r=subprocess.run(['scp','dombarker@100.108.41.90:'+H+'/evidence/RAW_GRAPH_ARCHIVE.json.xz',str(E/'RAW_GRAPH_ARCHIVE.json.xz')],capture_output=True)
assert r.returncode==0,r.stderr
raw=(E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes();assert hashlib.sha256(raw).hexdigest()==manifest['archive_sha256']
(E/'RAW_GRAPH_ARCHIVE.json.sha256').write_text(manifest['uncompressed_sha256']+'\n')
print('Strict raw audit:',len(results),'roots; graph archive bytes',len(raw))
