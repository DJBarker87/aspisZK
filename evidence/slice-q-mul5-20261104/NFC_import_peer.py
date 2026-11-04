from pathlib import Path
import subprocess,json,lzma,hashlib,base64
E=Path(__file__).resolve().parent;R=E.parent.parent
branch='codex/cx-slice-q-compose5-20261104';rev=subprocess.check_output(['git','rev-parse',branch],cwd=R,text=True).strip();prefix='evidence/slice-q-compose5-20261104/'
entries=subprocess.check_output(['git','ls-tree','-r',rev,prefix],cwd=R,text=True).splitlines()
records=[];blobs={}
for line in entries:
 mode,kind,rest=line.split(' ',2);oid,name=rest.split('\t',1)
 assert kind=='blob' and not name.endswith(('.olean','.elf','.o','.tar'))
 if oid not in blobs:
  data=subprocess.check_output(['git','cat-file','blob',oid],cwd=R)
  blobs[oid]=dict(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),base64=base64.b64encode(data).decode())
 records.append(dict(path=name,git_blob=oid))
payload=json.dumps(dict(revision=rev,branch=branch,files=records,blobs=blobs),sort_keys=True).encode();name='NFC_NFB_IMPORT.json'
(E/(name+'.xz')).write_bytes(lzma.compress(payload,preset=6));(E/(name+'.sha256')).write_text(hashlib.sha256(payload).hexdigest()+'  '+name+'\n')
get=lambda name:base64.b64decode(blobs[next(r['git_blob'] for r in records if r['path']==prefix+name)]['base64']).decode()
checker=get('NFB_source_checks.py');namespace={'__file__':str(E/'NFC_imported_NFB_source_checks.py'),'__name__':'NFC_imported_NFB_source_checks'}
exec(compile(checker,'NFB_source_checks.py','exec'),namespace)
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/verifier.rs'],cwd=R,text=True)
result=namespace['check'](source=get('NFB_geometry.rs.txt'),release=frozen)
manifest=dict(revision=rev,branch=branch,files=len(records),unique_blobs=len(blobs),archive=name+'.xz',uncompressed_sha256=hashlib.sha256(payload).hexdigest(),compressed_sha256=hashlib.sha256((E/(name+'.xz')).read_bytes()).hexdigest(),source_validation=result,credit='Source-only revalidation. No NFB final ledger/validator is committed at this revision. No sibling native/theorem credit promoted.',peer_worktree_touched=False)
(E/'NFC_NFB_PROVENANCE.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({k:manifest[k] for k in ['revision','files','unique_blobs','credit']}))
