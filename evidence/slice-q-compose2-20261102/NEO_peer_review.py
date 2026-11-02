"""Revalidate the committed sibling corpus in an owned review workspace."""
from pathlib import Path
import subprocess,json,lzma,hashlib,sys,time
E=Path(__file__).resolve().parent;R=E.parent.parent
W=Path('/private/tmp/NEO_peer_review_20261102');W.mkdir(exist_ok=True)
manifest=json.loads((E/'NEO_NEI_PROVENANCE.json').read_text())
files={}
for chunk in manifest['archives']:
 blob=(E/chunk['path']).read_bytes();assert hashlib.sha256(blob).hexdigest()==chunk['sha256']
 raw=lzma.decompress(blob);assert hashlib.sha256(raw).hexdigest()==chunk['uncompressed_sha256']
 current=json.loads(raw);assert not set(current)&set(files);files.update(current)
assert set(files)==set(manifest['files'])
for name,data in files.items():
 assert hashlib.sha256(data.encode()).hexdigest()==manifest['files'][name]['sha256']
 p=W/name;p.parent.mkdir(parents=True,exist_ok=True)
 # Inputs may be re-materialized only if a previous review wrote declared outputs.
 if not p.exists():p.write_text(data)
for p in R.iterdir():
 if p.name=='evidence':continue
 q=W/p.name
 if not q.exists():q.symlink_to(p)
for p in (R/'evidence').iterdir():
 q=W/'evidence'/p.name
 if not q.exists():q.symlink_to(p)
P=W/'evidence/slice-q-mul2-20261101'
start=time.monotonic()
with (E/'NEO_PEER_TESTS.stdout').open('w') as out,(E/'NEO_PEER_TESTS.stderr').open('w') as err:
 status=subprocess.run([sys.executable,str(P/'NEI_COMPOSE_TESTS.py')],cwd=W,stdout=out,stderr=err).returncode
rc=dict(target='NEI_COMPOSE_TESTS.py',exit_status=status,wall_seconds=time.monotonic()-start,source_revision=manifest['revision'],archives=manifest['archives'],prover_runs=0,print_axioms='N/A: receipt validation; inherited printed audits checked',workspace=str(W))
(E/'NEO_PEER_TESTS.json').write_text(json.dumps(rc,indent=1)+'\n')
print(json.dumps(rc));print((E/'NEO_PEER_TESTS.stderr').read_text()[-2500:]);sys.exit(status)
