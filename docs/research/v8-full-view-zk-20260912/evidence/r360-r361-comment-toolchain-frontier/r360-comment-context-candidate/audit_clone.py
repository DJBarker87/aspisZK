#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,stat,difflib
root=Path('/home/dombarker/project-offloads/aspis-r360-comment-context-candidate-20261002-a')
src=root/'src'; parent=Path('/home/dombarker/project-offloads/aspis-r349-output-name-alpha-candidate-20261002-a/src')
audit=root/'candidate-audit'; audit.mkdir(exist_ok=True)
manifest=json.loads((root/'R349-candidate-tree-manifest.json').read_text())
expected={row['path']:row for row in manifest}
sha=lambda b:hashlib.sha256(b).hexdigest()
def records(tree):
 out=[]
 for p in sorted(tree.rglob('*'),key=lambda x:x.relative_to(tree).as_posix()):
  rel=p.relative_to(tree).as_posix(); st=p.lstat(); mode=stat.S_IMODE(st.st_mode)
  if stat.S_ISLNK(st.st_mode): out.append({'path':rel,'kind':'symlink','target':os.readlink(p),'mode':mode})
  elif stat.S_ISDIR(st.st_mode): out.append({'path':rel,'kind':'directory','mode':mode})
  elif stat.S_ISREG(st.st_mode): out.append({'path':rel,'kind':'file','size':st.st_size,'sha256':sha(p.read_bytes()),'mode':mode})
  else: raise AssertionError(f'unexpected filesystem node {p}')
 return out
before=records(parent); current=records(src)
assert len(before)==len(expected)==1004,(len(before),len(expected))
base_map={x['path']:x for x in before}
expected_nonbuild={k:v for k,v in expected.items() if k != '_build' and not k.startswith('_build/')}
base_nonbuild={k:v for k,v in base_map.items() if k != '_build' and not k.startswith('_build/')}
assert base_nonbuild==expected_nonbuild,'R349 source files outside cached _build no longer match saved candidate manifest'
cm={x['path']:x for x in current}
assert cm.keys()==base_map.keys(),(len(cm),len(base_map),'path inventory mismatch')
changed=[path for path in base_map if cm[path]!=base_map[path]]
assert changed==['extract/ExtractTypes.ml'],changed
assert base_map['extract/ExtractTypes.ml']['sha256']=='cb59112741c428671764a44af7478117d2a324270ac0aec5c41052a3a2833a25'
assert cm['extract/ExtractTypes.ml']['sha256']=='0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527'
parent_inodes={(st.st_dev,st.st_ino) for p in parent.rglob('*') if p.is_file() for st in [p.stat()]}
cand_inodes={(st.st_dev,st.st_ino) for p in src.rglob('*') if p.is_file() for st in [p.stat()]}
shared=sorted(parent_inodes&cand_inodes)
assert not shared,shared[:20]
old=(audit/'ExtractTypes.before.ml').read_text(); new=(src/'extract/ExtractTypes.ml').read_text()
diff=''.join(difflib.unified_diff(old.splitlines(keepends=True),new.splitlines(keepends=True),fromfile='R349/extract/ExtractTypes.ml',tofile='R360/extract/ExtractTypes.ml'))
(audit/'ExtractTypes.patch.diff').write_text(diff)
(audit/'candidate-tree-manifest.json').write_text(json.dumps(current,indent=2)+'\n')
canonical=json.dumps(current,sort_keys=True,separators=(',',':')).encode()
out={'status':'candidate prepared only; not built or translated','parent_candidate_root':str(parent),'candidate_root':str(root),'R349_candidate_manifest_sha256':sha((root/'R349-candidate-tree-manifest.json').read_bytes()),'R349_prebuild_manifest_entries':len(expected),'R349_current_source_tree_entries':len(before),'R360_source_tree_entries':len(current),'R349_prebuild_manifest_matches_nonbuild_sources':True,'R360_cached_build_tree_matches_current_R349':all(cm[k]==base_map[k] for k in base_map if k.startswith('_build/') or k=='_build'),'changed_source_paths_vs_current_R349':changed,'only_ExtractTypes_changed':True,'R349_ExtractTypes_sha256':expected['extract/ExtractTypes.ml']['sha256'],'R360_ExtractTypes_sha256':cm['extract/ExtractTypes.ml']['sha256'],'R349_binary_sha256':sha((parent/'_build/default/main.exe').read_bytes()),'candidate_cached_main_exe_sha256':sha((src/'_build/default/main.exe').read_bytes()),'candidate_cached_executable_matches_R349':True,'shared_regular_file_inodes':len(shared),'R349_current_canonical_tree_sha256':sha(json.dumps(before,sort_keys=True,separators=(',',':')).encode()),'candidate_tree_manifest_sha256':sha((audit/'candidate-tree-manifest.json').read_bytes()),'candidate_canonical_tree_sha256':sha(canonical),'patch_sha256':sha(diff.encode()),'source_revision_of_R349_candidate':'56a931fc3879354a2fa584e73bd0a1d412714851','build_translation_or_Lean_compile_run':False}
(audit/'clone-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
