#!/usr/bin/env python3
"""Read-only local check of the prepared R356 source/audit bundle; does not build or launch."""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def H(p): return sha(Path(p).read_bytes())
old=ROOT/'source-r349/extract/ExtractTypes.ml'; new=ROOT/'source-r356/extract/ExtractTypes.ml'
old_bytes=old.read_bytes(); new_bytes=new.read_bytes(); old_text=old_bytes.decode(); new_text=new_bytes.decode()
old_hash='cb59112741c428671764a44af7478117d2a324270ac0aec5c41052a3a2833a25'
new_hash='2893509bb9fbbc159e9262532adab1d2b4f684b269f4e835d8cf5b6709188ddf'
assert H(old)==old_hash and H(new)==new_hash
before='''    | None, _ -> []
    | Some name, None ->
        [
          "Name pattern: ["
          ^ name_to_pattern_string (Some span) ctx.trans_ctx name
          ^ "]";
        ]
'''
insert='''    | None, _ -> []
    | Some name, _
      when List.exists (function Types.PeInstantiated _ -> true | _ -> false) name ->
        [
          "Instantiated source name: ["
          ^ name_to_string ctx.trans_ctx name
          ^ "]";
        ]
    | Some name, None ->
        [
          "Name pattern: ["
          ^ name_to_pattern_string (Some span) ctx.trans_ctx name
          ^ "]";
        ]
'''
assert old_text.count(before)==1
assert new_text==old_text.replace(before,insert)
for rel,expected in {
 'source-r349/TranslateCore.ml':'4f5db3cd77a10a3861539958d7b8566f09e6bcc3b72981fcc40388611d639cb9',
 'source-r356/TranslateCore.ml':'4f5db3cd77a10a3861539958d7b8566f09e6bcc3b72981fcc40388611d639cb9',
 'source-r349/interp/InterpExpansion.ml':'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19',
 'source-r356/interp/InterpExpansion.ml':'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19',
 'source-r349/PrePasses.ml':'09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd',
 'source-r356/PrePasses.ml':'09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd',
}.items(): assert H(ROOT/rel)==expected,(rel,H(ROOT/rel))
clone=json.loads((ROOT/'clone-audit.json').read_text())
assert clone['changed_source_paths_vs_current_R349']==['extract/ExtractTypes.ml']
assert clone['only_ExtractTypes_changed'] and clone['shared_regular_file_inodes']==0
assert clone['candidate_cached_executable_matches_R349']
manifest=json.loads((ROOT/'candidate-tree-manifest.json').read_text())
assert len(manifest)==1004
manifest_map={row['path']:row for row in manifest}
for rel, source_path in {
 'extract/ExtractTypes.ml':'source-r356/extract/ExtractTypes.ml',
 'TranslateCore.ml':'source-r356/TranslateCore.ml',
 'interp/InterpExpansion.ml':'source-r356/interp/InterpExpansion.ml',
 'PrePasses.ml':'source-r356/PrePasses.ml'}.items():
 assert manifest_map[rel]['sha256']==H(ROOT/source_path),(rel,manifest_map[rel]['sha256'],H(ROOT/source_path))
canonical=sha(json.dumps(manifest,sort_keys=True,separators=(',',':')).encode())
assert canonical==clone['candidate_canonical_tree_sha256']
assert clone['build_translation_or_Lean_compile_run'] is False
report={
 'status':'R356 source/candidate prepared for lead inspection; no build or translation',
 'candidate_root':clone['candidate_root'],
 'R349_source_revision':clone['source_revision_of_R349_candidate'],
 'current_worktree_revision_at_audit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT.parents[1],text=True).strip(),
 'parent_ExtractTypes_sha256':old_hash,'candidate_ExtractTypes_sha256':new_hash,
 'patch_sha256':clone['patch_sha256'],'candidate_tree_canonical_sha256':canonical,
 'candidate_tree_manifest_sha256':clone['candidate_tree_manifest_sha256'],
 'source_files_unchanged':{
  'TranslateCore.ml':H(ROOT/'source-r356/TranslateCore.ml'),
  'InterpExpansion.ml':H(ROOT/'source-r356/interp/InterpExpansion.ml'),
  'PrePasses.ml':H(ROOT/'source-r356/PrePasses.ml')},
 'shared_regular_file_inodes':clone['shared_regular_file_inodes'],
 'cached_R349_executable_sha256':clone['candidate_cached_main_exe_sha256'],
 'edited_source_paths':clone['changed_source_paths_vs_current_R349'],
 'route_boundary':'The inserted case is confined to extract_comment_with_span. Existing NameMatcher calls in extract_attributes, all other helper functions, comments for non-instantiated names, and all source metadata are byte-preserved by exact reconstruction.',
 'execution_status':'not built, not translated, not Lean-compiled; R223-owned launcher is outside this source audit and was not invoked.'}
(ROOT/'source-bundle-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
