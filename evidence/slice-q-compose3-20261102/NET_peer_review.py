"""Review immutable peer Git blobs in an owned workspace, without prover replay."""
from pathlib import Path
import sys,subprocess,json,lzma,hashlib,base64,time
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;W=Path('/private/tmp/NET_peer_5d12713_20261103')
p=json.loads((E/'NET_NEI_PROVENANCE.json').read_text());files={}
for a in p['archives']:
 raw=(E/a['path']).read_bytes();assert hashlib.sha256(raw).hexdigest()==a['sha256']
 plain=lzma.decompress(raw);assert hashlib.sha256(plain).hexdigest()==a['uncompressed_sha256']
 current=json.loads(plain)
 if a.get('role')!='update':assert not set(files)&set(current)
 files.update(current)
for name in p['deleted_paths']:files.pop(name,None)
assert set(files)==set(p['files'])
W.mkdir(exist_ok=True)
for name,value in files.items():
 raw=value.encode() if isinstance(value,str) else base64.b64decode(value['base64']);pin=p['files'][name]
 assert hashlib.sha256(raw).hexdigest()==pin['sha256']
 assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==pin['git_blob']
 q=W/name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
for q in R.iterdir():
 if q.name=='evidence':continue
 link=W/q.name
 if not link.exists():link.symlink_to(q)
for q in (R/'evidence').iterdir():
 link=W/'evidence'/q.name
 if not link.exists():link.symlink_to(q)
# Keep validator Python sources as regular byte-identical copies, so their
# __file__.resolve() uses this isolated review root rather than a data symlink.
B=W/'evidence/slice-q-compose-20261029'
if B.is_symlink():
 B.unlink();B.mkdir()
 for original in (R/'evidence/slice-q-compose-20261029').iterdir():
  target=B/original.name
  if original.is_file() and original.suffix=='.py':target.write_bytes(original.read_bytes())
  else:target.symlink_to(original)
P=W/p['source_prefix'];code=f'''from pathlib import Path
import sys,json
sys.dont_write_bytecode=True
sys.path.insert(0,{str(P)!r})
import NEI_composition as c
base=c.obj(c.E.parent/'native-ledger3-20261029/NDT_LEDGER.json');edges=c.prepare(base);out,delta=c.validate(base,edges)
rows=[r for r in out['rows'] if r['composed_status']=='CLOSED']
Path({str(E/'NET_PEER_POSITIVE.json')!r}).write_text(json.dumps(dict(delta=delta,rows=rows,edges=[e for e in edges['edges'] if e['status']=='CLOSED'],row_certificates=edges['row_certificates']),indent=1)+'\\n')
print(json.dumps(delta))
'''
start=time.monotonic()
with (E/'NET_PEER_POSITIVE.stdout').open('w') as out,(E/'NET_PEER_POSITIVE.stderr').open('w') as err:r=subprocess.run([sys.executable,'-c',code],cwd=W,stdout=out,stderr=err)
receipt=dict(exit_status=r.returncode,wall_seconds=time.monotonic()-start,source_revision=p['revision'],command='Unchanged committed NEI_composition.prepare + validate on NDT copy',prover_runs=0,workspace=str(W),files=len(files),partial_or_WIP_credit=False)
(E/'NET_PEER_POSITIVE_RECEIPT.json').write_text(json.dumps(receipt,indent=1)+'\n');print(json.dumps(receipt));print((E/'NET_PEER_POSITIVE.stderr').read_text()[-1800:]);sys.exit(r.returncode)
