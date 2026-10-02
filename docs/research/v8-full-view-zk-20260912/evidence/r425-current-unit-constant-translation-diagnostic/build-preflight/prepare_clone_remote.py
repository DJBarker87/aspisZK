#!/usr/bin/env python3
"""Preparation only: ordinary-copy the R424 cached compiler tree for R425."""
import hashlib,json,os,shutil,stat,time
from pathlib import Path
SRC=Path('/home/dombarker/project-offloads/aspis-r424-concrete-associated-types-candidate-20261002-a')
DST=Path('/home/dombarker/project-offloads/aspis-r425-unit-constant-candidate-20261002-a')
OUT=Path('/tmp/aspis-r425-preclone-audit.json')
EXPECTED='579f332212ad75b386b088ef7835783f7cb84a835b1acb96031d49847fc53a17'
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
def scan(root):
 rows=[]
 for current,dirs,files in os.walk(root,topdown=True,followlinks=False):
  dirs.sort();files.sort(); base=Path(current)
  for name in list(dirs):
   p=base/name; rel=str(p.relative_to(root)); st=p.lstat()
   if stat.S_ISLNK(st.st_mode):
    rows.append({'path':rel,'kind':'symlink','target':os.readlink(p),'mode':stat.S_IMODE(st.st_mode)})
    dirs.remove(name)
   else: rows.append({'path':rel,'kind':'directory','mode':stat.S_IMODE(st.st_mode)})
  for name in files:
   p=base/name; rel=str(p.relative_to(root)); st=p.lstat()
   if stat.S_ISLNK(st.st_mode):rows.append({'path':rel,'kind':'symlink','target':os.readlink(p),'mode':stat.S_IMODE(st.st_mode)})
   elif stat.S_ISREG(st.st_mode):rows.append({'path':rel,'kind':'file','size':st.st_size,'sha256':digest(p),'mode':stat.S_IMODE(st.st_mode),'mtime_ns':st.st_mtime_ns,'dev':st.st_dev,'ino':st.st_ino})
   else:rows.append({'path':rel,'kind':'other','mode':stat.S_IMODE(st.st_mode),'mode_type':stat.S_IFMT(st.st_mode)})
 return rows
assert SRC.is_dir(),f'missing source root: {SRC}'
assert not DST.exists(),f'destination already exists: {DST}'
pre=shutil.disk_usage(DST.parent)
started=time.monotonic()
source_rows=scan(SRC)
prepass=SRC/'src/PrePasses.ml'
assert digest(prepass)==EXPECTED,('R424 parent PrePasses SHA mismatch',digest(prepass))
assert digest(SRC/'src/interp/InterpUtils.ml')=='8b885a725def3c7a923cc634f05a7b91bd25b4334b62b2ba6a1d09faf0d8a65a'
assert digest(SRC/'aeneas-r424-concrete-associated-types-candidate')=='bb49c46a2a3fde0b101571de5b13158a516e668b65cc2235166af830a29a47ea'
shutil.copytree(SRC,DST,symlinks=True,copy_function=shutil.copy2)
clone_rows=scan(DST)
elapsed=time.monotonic()-started
# Compare full cloned tree content/type/permissions. Ignore only host inode/device in this equality view.
def portable(row):return {k:v for k,v in row.items() if k not in ('dev','ino')}
assert [portable(x) for x in source_rows]==[portable(x) for x in clone_rows], 'copied tree manifest differs before overlay'
src_files={x['path']:x for x in source_rows if x['kind']=='file'}
dst_files={x['path']:x for x in clone_rows if x['kind']=='file'}
shared=[]
for path,row in src_files.items():
 other=dst_files[path]
 if row['dev']==other['dev'] and row['ino']==other['ino']:shared.append(path)
assert not shared,('shared regular file inodes',shared[:10])
assert scan(SRC)==source_rows,'parent changed during copy'
record={
 'status':'ordinary copy completed; source patch not yet applied; no compiler build',
 'parent_root':str(SRC),'candidate_root':str(DST),
 'source_entry_count':len(source_rows),'candidate_entry_count':len(clone_rows),
 'regular_file_count':len(src_files),'symlink_count':sum(x['kind']=='symlink' for x in source_rows),
 'parent_prepasses_sha256':digest(prepass),'expected_parent_prepasses_sha256':EXPECTED,
 'content_and_mode_manifest_equal_before_patch':True,'shared_regular_file_inode_count':len(shared),
 'copy_wall_seconds':round(elapsed,3),'destination_parent_free_bytes_before_copy':pre.free,
 'source_inventory':source_rows,'clone_inventory':clone_rows,
 'candidate_prepass_before_overlay':{'sha256':digest(DST/'src/PrePasses.ml'),'path':str(DST/'src/PrePasses.ml')}
}
OUT.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ('source_inventory','clone_inventory')},indent=2))
print('AUDIT_JSON',str(OUT))
