#!/usr/bin/env python3
"""Read-only local check of the prepared R360 source bundle; does not build or launch."""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def H(p): return sha(Path(p).read_bytes())
old=ROOT/'source-r349/extract/ExtractTypes.ml'; new=ROOT/'source-r360/extract/ExtractTypes.ml'
old_text=old.read_text(); new_text=new.read_text()
old_hash='cb59112741c428671764a44af7478117d2a324270ac0aec5c41052a3a2833a25'
new_hash='0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527'
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
          ^ name_to_string ctx name
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
expected_files={
 'source-r349/TranslateCore.ml':'4f5db3cd77a10a3861539958d7b8566f09e6bcc3b72981fcc40388611d639cb9',
 'source-r360/TranslateCore.ml':'4f5db3cd77a10a3861539958d7b8566f09e6bcc3b72981fcc40388611d639cb9',
 'source-r349/interp/InterpExpansion.ml':'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19',
 'source-r360/interp/InterpExpansion.ml':'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19',
 'source-r349/PrePasses.ml':'09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd',
 'source-r360/PrePasses.ml':'09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd',
 'source-r349/extract/ExtractBase.ml':'7209c8454b68c63a838efadb52e9b82ad58a646eabebcfb58c6b4161ee92a0c0',
 'source-r360/extract/ExtractBase.ml':'7209c8454b68c63a838efadb52e9b82ad58a646eabebcfb58c6b4161ee92a0c0'}
for rel,expected in expected_files.items(): assert H(ROOT/rel)==expected,(rel,H(ROOT/rel))
clone=json.loads((ROOT/'clone-audit.json').read_text())
assert clone['changed_source_paths_vs_current_R349']==['extract/ExtractTypes.ml']
assert clone['only_ExtractTypes_changed'] and clone['shared_regular_file_inodes']==0
assert clone['candidate_cached_executable_matches_R349']
manifest=json.loads((ROOT/'candidate-tree-manifest.json').read_text()); assert len(manifest)==1004
manifest_map={row['path']:row for row in manifest}
for rel,source_path in {'extract/ExtractTypes.ml':'source-r360/extract/ExtractTypes.ml','extract/ExtractBase.ml':'source-r360/extract/ExtractBase.ml','TranslateCore.ml':'source-r360/TranslateCore.ml','interp/InterpExpansion.ml':'source-r360/interp/InterpExpansion.ml','PrePasses.ml':'source-r360/PrePasses.ml'}.items():
 assert manifest_map[rel]['sha256']==H(ROOT/source_path),(rel,manifest_map[rel]['sha256'],H(ROOT/source_path))
canonical=sha(json.dumps(manifest,sort_keys=True,separators=(',',':')).encode())
assert canonical==clone['candidate_canonical_tree_sha256']
assert clone['build_translation_or_Lean_compile_run'] is False
report={
 'status':'R360 source/candidate prepared for lead inspection; no build or translation',
 'candidate_root':clone['candidate_root'],
 'R349_source_revision':clone['source_revision_of_R349_candidate'],
 'current_worktree_revision_at_audit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT.parents[1],text=True).strip(),
 'R349_ExtractTypes_sha256':old_hash,'R360_ExtractTypes_sha256':new_hash,
 'patch_sha256':clone['patch_sha256'],'candidate_tree_canonical_sha256':canonical,
 'candidate_tree_manifest_sha256':clone['candidate_tree_manifest_sha256'],
 'unchanged_source_hashes':{k.split('/')[-1]:H(ROOT/k) for k in expected_files if 'source-r360/' in k},
 'ExtractBase_name_to_string_source':{'file_sha256':H(ROOT/'source-r360/extract/ExtractBase.ml'),'decl_line_start':634,'source_text':'let name_to_string (ctx : extraction_ctx) =\n  PrintPure.name_to_string (extraction_ctx_to_fmt_env ctx)','call_sites':'ExtractTypes.ml lines 833, 845, 905 use `name_to_string ctx def.item_meta.name`; the R360 branch follows this local extraction_ctx API.'},
 'shared_regular_file_inodes':clone['shared_regular_file_inodes'],
 'cached_R349_executable_sha256':clone['candidate_cached_main_exe_sha256'],
 'changed_source_paths':clone['changed_source_paths_vs_current_R349'],
 'scope':'One comment-constructor match case only. Existing pattern helpers and extract_attributes behavior are byte-preserved by exact reconstruction.',
 'execution_status':'not built, not translated, not Lean-compiled; no source correspondence or semantic claim.'}
(ROOT/'source-bundle-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
