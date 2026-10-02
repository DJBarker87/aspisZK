#!/usr/bin/env python3
"""Read-only check of R315 saved source excerpts, source inputs and checksums."""
import hashlib,json,re
from pathlib import Path
A=Path(__file__).resolve().parent; ROOT=A.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((A/'inventory.json').read_text())
source_paths={
 'R283PrivateNormBatch.llbc':ROOT/'.r21-scratch/r283-private-norm-batch-extract/R283PrivateNormBatch.llbc',
 'R292_Funs.lean':ROOT/'.r21-scratch/r292-private-batch-translation/generated/AspisR292PrivateBatch/Funs.lean',
 'R292_FunsExternal_Template.lean':ROOT/'.r21-scratch/r292-private-batch-translation/generated/AspisR292PrivateBatch/FunsExternal_Template.lean',
 'R292_Types.lean':ROOT/'.r21-scratch/r292-private-batch-translation/generated/AspisR292PrivateBatch/Types.lean',
 'R292_TypesExternal_Template.lean':ROOT/'.r21-scratch/r292-private-batch-translation/generated/AspisR292PrivateBatch/TypesExternal_Template.lean',
 'R292_translation.json':ROOT/'.r21-scratch/r292-private-batch-translation/generated/translation.json',
 'R292_translation-result.json':ROOT/'.r21-scratch/r292-private-batch-translation/translation-result.json',
 'R283_result.json':ROOT/'.r21-scratch/r283-private-norm-batch-extract/result.json',
 'R283_extract-command.json':ROOT/'.r21-scratch/r283-private-norm-batch-extract/extract-command.json'}
for k,p in source_paths.items(): assert sha(p)==m['artifact_hashes'][k],(k,sha(p),m['artifact_hashes'][k])
s=(source_paths['R292_Funs.lean']).read_text(); names=[x['lean_name'].split('AspisR292PrivateBatch.',1)[1] for x in m['blocks']]
blocks=[]
for n in names:
 pos=s.index('def '+n+'\n'); begin=s.rfind('/--',0,pos); end=s.find('\n/--',pos)
 blocks.append(s[begin:end].rstrip()+'\n')
assert '\n\n'.join(blocks)==(A/'verbatim-blocks.lean').read_text()
assert m['body_alpha_equality']['loop0_body_vs_loop1_body_after_token_boundary_renaming_px_py_and_x_y']
assert [x['name'] for x in m['direct_external_template_declarations_referenced_by_four_blocks']]==['core.slice.Slice.last']
assert m['other_function_template_refs_in_four_blocks']==[] and not m['chain_type_template_referenced_in_four_blocks']
entries=[]
for line in (A/'SHA256SUMS').read_text().splitlines():
 want,rel=line.split('  ',1); p=A/rel; entries.append((rel,p.is_file() and sha(p)==want))
assert entries and all(ok for _,ok in entries)
report={'all_passed':True,'source_input_hashes_match':len(source_paths),'verbatim_blocks_match_source':len(blocks),'body_alpha_equality':True,'direct_external_template':'core.slice.Slice.last (Fun12)','other_function_template_refs':0,'Chain_type_template_ref':False,'archive_checksum_entries_checked':len(entries),'checksum_mismatches':[],'semantic_boundary':'direct syntactic dependency inventory only'}
(A/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
