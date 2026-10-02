#!/usr/bin/env python3
"""Clone and minimally patch the cached R289 source tree; no build/translation."""
import difflib, hashlib, json, os, pathlib, shutil, stat, subprocess
PARENT=pathlib.Path('/home/dombarker/project-offloads/aspis-r289-retention-candidate-20261002-a/src')
ROOT=pathlib.Path('/home/dombarker/project-offloads/aspis-r312-slice-length-candidate-20261002-a')
CAND=ROOT/'src'; AUD=ROOT/'candidate-audit'
AUD.mkdir(parents=True,exist_ok=True)
assert PARENT.is_dir() and not CAND.exists(), str(CAND)

def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''): h.update(block)
 return h.hexdigest()

def tree(root):
 records=[]; inodes=set()
 for parent,dirs,files in os.walk(root,topdown=True,followlinks=False):
  base=pathlib.Path(parent)
  for name in sorted(dirs+files):
   p=base/name; rel=p.relative_to(root).as_posix(); st=p.lstat()
   if stat.S_ISLNK(st.st_mode):
    records.append({'path':rel,'kind':'symlink','target':os.readlink(p),'mode':stat.S_IMODE(st.st_mode)})
   elif stat.S_ISDIR(st.st_mode):
    records.append({'path':rel,'kind':'directory','mode':stat.S_IMODE(st.st_mode)})
   elif stat.S_ISREG(st.st_mode):
    records.append({'path':rel,'kind':'file','size':st.st_size,'sha256':digest(p),'mode':stat.S_IMODE(st.st_mode)})
    inodes.add((st.st_dev,st.st_ino))
   else:
    raise RuntimeError(f'unexpected filesystem object: {rel}, mode={oct(st.st_mode)}')
 records.sort(key=lambda x:x['path'])
 serial=json.dumps(records,sort_keys=True,separators=(',',':')).encode()
 return {'records':records,'tree_sha256':hashlib.sha256(serial).hexdigest(),'regular_file_inode_count':len(inodes),'inodes':inodes}

parent_before=tree(PARENT)
subprocess.run(['/bin/cp','-a',str(PARENT),str(CAND)],check=True)
clone_before=tree(CAND)
shared=parent_before['inodes'] & clone_before['inodes']
assert not shared, f'shared regular file inodes: {len(shared)}'
assert parent_before['records']==clone_before['records'], 'clone differs before patch'
pre={'parent_source':str(PARENT),'candidate_source':str(CAND),'parent_tree_sha256':parent_before['tree_sha256'],'candidate_prepatch_tree_sha256':clone_before['tree_sha256'],'tree_hashes_equal':parent_before['tree_sha256']==clone_before['tree_sha256'],'full_path_record_equality':parent_before['records']==clone_before['records'],'parent_entry_count':len(parent_before['records']),'regular_file_count':parent_before['regular_file_inode_count'],'shared_regular_file_inodes':0,'candidate_has_cached_build':(CAND/'_build').is_dir(),'cached_build_file_count':sum(1 for p in (CAND/'_build').rglob('*') if p.is_file()),'parent_prepass_sha256':digest(PARENT/'PrePasses.ml')}
(AUD/'prepatch-clone-audit.json').write_text(json.dumps(pre,indent=2)+'\n')
(AUD/'parent-tree-manifest.json').write_text(json.dumps(parent_before['records'],indent=2)+'\n')
(AUD/'candidate-prepatch-tree-manifest.json').write_text(json.dumps(clone_before['records'],indent=2)+'\n')

file=CAND/'PrePasses.ml'; before=file.read_text()
old='''      (* Some slice patterns lower directly to a metadata read on a shared safe
         slice reference, without an intermediate raw pointer.  This is the
         same length operation and can be rewritten without any use analysis. *)
      let direct_metadata_rewriter =
        object
          inherit [_] map_statement as super

          method! visit_statement env st =
            match st.kind with
            | Assign
                (dest, Use ((Copy metadata_place | Move metadata_place), _retag))
              when dest.ty = mk_usize_ty && metadata_place.ty = mk_usize_ty -> (
                match metadata_place.kind with
                | PlaceProjection
                    ( ({ ty = TRef (_, TSlice elem_ty, RShared); _ } as reference),
                      PtrMetadata ) ->
                    { st with kind = slice_len_call st dest reference elem_ty }
                | _ -> super#visit_statement env st)
            | _ -> super#visit_statement env st
        end
'''
new='''      (* A safe shared-slice length operation can be represented either as a
         direct metadata read or as Len of a dereferenced shared slice. Both
         lower to the existing slice_len_fn call, preserving the statement span. *)
      let direct_metadata_rewriter =
        object
          inherit [_] map_statement as super

          method! visit_statement env st =
            match st.kind with
            | Assign
                ( dest,
                  Len
                    ( { kind = PlaceProjection (reference, Deref);
                        ty = TSlice elem_ty },
                      TSlice len_elem_ty,
                      None ) )
              when dest.ty = mk_usize_ty && elem_ty = len_elem_ty -> (
                match reference.ty with
                | TRef (_, TSlice reference_elem_ty, RShared)
                  when reference_elem_ty = elem_ty ->
                    { st with kind = slice_len_call st dest reference elem_ty }
                | _ -> super#visit_statement env st)
            | Assign
                (dest, Use ((Copy metadata_place | Move metadata_place), _retag))
              when dest.ty = mk_usize_ty && metadata_place.ty = mk_usize_ty -> (
                match metadata_place.kind with
                | PlaceProjection
                    ( ({ ty = TRef (_, TSlice elem_ty, RShared); _ } as reference),
                      PtrMetadata ) ->
                    { st with kind = slice_len_call st dest reference elem_ty }
                | _ -> super#visit_statement env st)
            | _ -> super#visit_statement env st
        end
'''
assert before.count(old)==1, f'expected exact unique direct rewriter block, found {before.count(old)}'
after=before.replace(old,new,1)
file.write_text(after)
post=tree(CAND); parent_after=tree(PARENT)
assert parent_after['records']==parent_before['records'] and parent_after['tree_sha256']==parent_before['tree_sha256'], 'parent tree changed'
# Precisely locate path-level content changes against the prepatch clone.
def bypath(records): return {r['path']:r for r in records}
pre_map=bypath(clone_before['records']); post_map=bypath(post['records'])
changed=[k for k in sorted(set(pre_map)|set(post_map)) if pre_map.get(k)!=post_map.get(k)]
assert changed==['PrePasses.ml'], changed
assert post['inodes'].isdisjoint(parent_after['inodes']), 'postpatch source unexpectedly shares a regular file inode with parent'
parent_prepass=(PARENT/'PrePasses.ml').read_text().splitlines(keepends=True)
candidate_prepass=after.splitlines(keepends=True)
diff=''.join(difflib.unified_diff(parent_prepass,candidate_prepass,fromfile='a/PrePasses.ml (R289 parent)',tofile='b/PrePasses.ml (R312 candidate)'))
(AUD/'PrePasses.patch').write_text(diff)
shutil.copy2(PARENT/'PrePasses.ml',AUD/'PrePasses.parent.ml')
shutil.copy2(file,AUD/'PrePasses.candidate.ml')
(AUD/'candidate-tree-manifest.json').write_text(json.dumps(post['records'],indent=2)+'\n')
report={'parent_source_path':str(PARENT),'candidate_source_path':str(CAND),'parent_tree_sha256_before':parent_before['tree_sha256'],'candidate_tree_sha256_before_patch':clone_before['tree_sha256'],'parent_tree_sha256_after':parent_after['tree_sha256'],'candidate_tree_sha256_after_patch':post['tree_sha256'],'parent_candidate_byte_identical_before_patch':parent_before['records']==clone_before['records'],'parent_tree_unchanged':parent_after['records']==parent_before['records'],'shared_regular_file_inodes_before_or_after':0,'source_path_entry_count':len(parent_before['records']),'source_regular_file_count':parent_before['regular_file_inode_count'],'candidate_cached_build_preserved':(CAND/'_build').is_dir(),'candidate_cached_build_file_count':pre['cached_build_file_count'],'changed_paths_after_patch':changed,'parent_PrePasses_sha256':digest(PARENT/'PrePasses.ml'),'candidate_PrePasses_sha256':digest(file),'patch_sha256':hashlib.sha256(diff.encode()).hexdigest(),'patch_only_changes_direct_metadata_rewriter':True,'translation_or_build_run':False}
(AUD/'postpatch-tree-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
