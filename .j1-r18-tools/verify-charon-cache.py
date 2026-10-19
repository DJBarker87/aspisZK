from pathlib import Path
import hashlib,json,subprocess,tomllib,tarfile
w=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((w/'charon-metadata-linux.json').read_text())
lock=tomllib.loads((w/'charon/charon/Cargo.lock').read_text());locked={(p['name'],p['version'],p.get('source')):p for p in lock['package']}
rows=[]
for p in m['packages']:
 root=Path(p['manifest_path']).parent;src=p['source'];row={'id':p['id'],'manifest':p['manifest_path'],'manifest_sha256':sha(Path(p['manifest_path'])),'source':src}
 if src and src.startswith('registry+'):
  lk=locked[(p['name'],p['version'],src)]
  archive=root.parents[2]/'cache'/root.parent.name/(root.name+'.crate')
  assert sha(archive)==lk['checksum'],p['id']
  count=0
  with tarfile.open(archive) as t:
   for member in t:
    if member.isfile():
     rel=Path(member.name).relative_to(root.name)
     assert (root/rel).read_bytes()==t.extractfile(member).read(),(p['id'],str(rel));count+=1
    elif not member.isdir():raise ValueError('Unexpected registry archive member '+member.name)
  row.update(archive=str(archive),package_checksum=lk['checksum'],verified_source_files=count)
 elif src and src.startswith('git+'):
  head=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip()
  assert head==src.split('#')[-1],p['id']
  assert subprocess.check_output(['git','-C',str(root),'status','--porcelain','--untracked-files=no'],text=True)==''
  row.update(git_head=head,tracked_clean=True)
 elif src is None:assert str(root).startswith(str(w/'charon/charon'))
 else:raise ValueError(src)
 rows.append(row)
r={'scope':'Read/hash-only dependency cache attestation before exact-source native build','cargo_lock_sha256':sha(w/'charon/charon/Cargo.lock'),'metadata_sha256':sha(w/'charon-metadata-linux.json'),'packages':rows}
(w/'charon-dependency-pins.json').write_text(json.dumps(r,indent=2)+'\n')
print(len(rows),'locked Linux packages attested')
