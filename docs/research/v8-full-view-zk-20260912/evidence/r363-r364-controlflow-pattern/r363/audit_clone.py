#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,stat,difflib
base=Path('/home/dombarker/project-offloads/aspis-r360-comment-context-candidate-20261002-a')
root=Path('/home/dombarker/project-offloads/aspis-r363-instantiated-pattern-candidate-20261002-a')
src=root/'src'; base_src=base/'src'
audit=root/'candidate-audit'; audit.mkdir(exist_ok=True)
base_audit=json.loads((base/'candidate-audit/clone-audit.json').read_text())
build_result=json.loads((base/'candidate-audit/build-result.json').read_text())
expected=json.loads((base/'candidate-audit/candidate-tree-manifest.json').read_text())
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
base_current=records(base_src); current=records(src)
base_nonbuild=[r for r in base_current if not (r['path']=='_build' or r['path'].startswith('_build/'))]
expected_nonbuild=[r for r in expected if not (r['path']=='_build' or r['path'].startswith('_build/'))]
assert base_nonbuild==expected_nonbuild, 'R360 non-build source tree differs from saved R360 manifest'
base_map={x['path']:x for x in base_current}; cm={x['path']:x for x in current}
assert cm.keys()==base_map.keys(), (len(cm),len(base_map),'path inventory mismatch')
changed=[path for path in base_map if cm[path]!=base_map[path]]
assert changed==['NameMatcher.ml','llbc/LlbcAstUtils.ml'],changed
assert base_map['NameMatcher.ml']['sha256']=='32c60e5ad98d4953790d2a4be557229be66951738ef8c4f8b25a170db21c4cef'
assert cm['NameMatcher.ml']['sha256']=='bdafe5b3f4a688d0fa0b4df7f2e8a3d907f70be9fdaf64420ea600ceab597aa8'
assert cm['llbc/LlbcAstUtils.ml']['sha256']=='17cb1b5cd3e0cf119f4c4eee776e0fc49e2a39c6ee7abbaa339f70d466484b97'
base_inodes={(p.stat().st_dev,p.stat().st_ino) for p in base_src.rglob('*') if p.is_file()}
cand_inodes={(p.stat().st_dev,p.stat().st_ino) for p in src.rglob('*') if p.is_file()}
shared=sorted(base_inodes&cand_inodes)
assert not shared, shared[:20]
assert sha((src/'_build/default/main.exe').read_bytes())==build_result['binary_sha256']
old=(audit/'NameMatcher.before.ml'); old.write_bytes((base_src/'NameMatcher.ml').read_bytes())
new=(src/'NameMatcher.ml').read_text()
diff=''.join(difflib.unified_diff(old.read_text().splitlines(keepends=True),new.splitlines(keepends=True),fromfile='R360/src/NameMatcher.ml',tofile='R363/src/NameMatcher.ml'))
(audit/'NameMatcher.patch.diff').write_text(diff)
(audit/'R360-source-tree-manifest.json').write_bytes(json.dumps(base_current,indent=2).encode()+b'\n')
(audit/'R363-source-tree-manifest.json').write_bytes(json.dumps(current,indent=2).encode()+b'\n')
canonical=json.dumps(current,sort_keys=True,separators=(',',':')).encode()
canonical_base=json.dumps(base_current,sort_keys=True,separators=(',',':')).encode()
out={'status':'candidate source overlay prepared only; not built or translated','parent_root':str(base),'candidate_root':str(root),'base_R360_audit_sha256':sha((base/'candidate-audit/clone-audit.json').read_bytes()),'R360_saved_source_manifest_sha256':sha((base/'candidate-audit/candidate-tree-manifest.json').read_bytes()),'R360_source_tree_entries':len(base_current),'R363_source_tree_entries':len(current),'R360_nonbuild_sources_match_saved_manifest':True,'changed_source_paths_vs_R360':['src/'+p for p in changed],'only_requested_overlay_files_changed':True,'source_hashes':{'R360_NameMatcher_ml_sha256':base_map['NameMatcher.ml']['sha256'],'R363_NameMatcher_ml_sha256':cm['NameMatcher.ml']['sha256'],'R360_LlbcAstUtils_ml_sha256':base_map['llbc/LlbcAstUtils.ml']['sha256'],'R363_LlbcAstUtils_ml_sha256':cm['llbc/LlbcAstUtils.ml']['sha256'],'ExtractTypes_ml_sha256':cm['extract/ExtractTypes.ml']['sha256'],'TranslateCore_ml_sha256':cm['TranslateCore.ml']['sha256'],'InterpExpansion_ml_sha256':cm['interp/InterpExpansion.ml']['sha256'],'PrePasses_ml_sha256':cm['PrePasses.ml']['sha256']},'R360_cached_binary_sha256':build_result['binary_sha256'],'R363_cached_binary_sha256':sha((src/'_build/default/main.exe').read_bytes()),'cached_binary_unchanged':True,'shared_regular_file_inodes':len(shared),'R360_canonical_tree_sha256':sha(canonical_base),'R363_canonical_tree_sha256':sha(canonical),'R363_tree_manifest_sha256':sha((audit/'R363-source-tree-manifest.json').read_bytes()),'overlay_diff_sha256':sha(diff.encode()),'source_revision':'R360 clone is source snapshot without Git metadata; campaign source revision is recorded by launcher','build_or_translation_run':False}
(audit/'clone-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
