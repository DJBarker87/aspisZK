from pathlib import Path
import hashlib,json,re
root=Path('.r21-scratch'); out=root/'r315-batch-prefix-loop-inventory'
funs=root/'r292-private-batch-translation/generated/AspisR292PrivateBatch/Funs.lean'; s=funs.read_text()
names=['circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0.body','circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0','circle_norm.joined_inverse.line_norm.r110_norm.batch_loop1.body','circle_norm.joined_inverse.line_norm.r110_norm.batch_loop1']
blocks={}
for name in names:
 pos=s.index('def '+name+'\n'); begin=s.rfind('/--',0,pos); end=s.find('\n/--',pos)
 blocks[name]=s[begin:end].rstrip()+'\n'
(out/'verbatim-blocks.lean').write_text('\n\n'.join(blocks[n] for n in names))
def body(b):
 b=b.split(':= do',1)[1]
 for a,c in [('px1','OUT'),('py1','OUT'),('px','PREF'),('py','PREF'),('x','ITEM'),('y','ITEM')]: b=re.sub(r'\b'+a+r'\b',c,b)
 return b.strip()
body_eq=body(blocks[names[0]])==body(blocks[names[2]])
tr=json.loads((root/'r292-private-batch-translation/generated/translation.json').read_text())
trres=json.loads((root/'r292-private-batch-translation/translation-result.json').read_text())
source_hashes=json.loads((root/'r283-private-norm-batch-extract/result.json').read_text())['source_hashes']
last={'name':'core.slice.Slice.last','provider':'R292 external function template axiom','def_id':12,'lean_name':'AspisR292PrivateBatch.core.slice.Slice.last','lean_file':'AspisR292PrivateBatch/FunsExternal_Template.lean','rust_source_span':'core/src/slice/mod.rs:281:4-281:42'}
call_body=[
 {'name':'core.slice.iter.IteratorSliceIter.next','provider':'Aeneas.Std support symbol; not listed among R292 external template declarations'},
 {'name':'alloc.vec.Vec.deref','provider':'Aeneas.Std support symbol; not listed among R292 external template declarations'},last,
 {'name':'core.option.Option.unwrap','provider':'Aeneas.Std support symbol; not listed among R292 external template declarations'},
 {'name':'circle_norm.joined_inverse.line_norm.r110_norm.B.mul','provider':'R292 generated function','def_id':14,'lean_name':'AspisR292PrivateBatch.circle_norm.joined_inverse.line_norm.r110_norm.B.mul','lean_file':'AspisR292PrivateBatch/Funs.lean'},
 {'name':'alloc.vec.Vec.push','provider':'Aeneas.Std support symbol; not listed among R292 external template declarations'}]
typed_body=['core.slice.iter.Iter circle_norm.joined_inverse.line_norm.r110_norm.B','alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B','Result (ControlFlow ((Iter B) × (Vec B)) (Vec B))','Option B (via core.slice.Slice.last and Option.unwrap)']
inputs={'R283PrivateNormBatch.llbc':root/'r283-private-norm-batch-extract/R283PrivateNormBatch.llbc','R292_Funs.lean':funs,'R292_FunsExternal_Template.lean':root/'r292-private-batch-translation/generated/AspisR292PrivateBatch/FunsExternal_Template.lean','R292_Types.lean':root/'r292-private-batch-translation/generated/AspisR292PrivateBatch/Types.lean','R292_TypesExternal_Template.lean':root/'r292-private-batch-translation/generated/AspisR292PrivateBatch/TypesExternal_Template.lean','R292_translation.json':root/'r292-private-batch-translation/generated/translation.json','R292_translation-result.json':root/'r292-private-batch-translation/translation-result.json','R283_result.json':root/'r283-private-norm-batch-extract/result.json','R283_extract-command.json':root/'r283-private-norm-batch-extract/extract-command.json'}
typed={'loop0.body':typed_body,'loop0':['core.slice.iter.Iter B','alloc.vec.Vec B','Result (alloc.vec.Vec B)','loop state (Iter B × Vec B)'],'loop1.body':typed_body,'loop1':['core.slice.iter.Iter B','alloc.vec.Vec B','Result (alloc.vec.Vec B)','loop state (Iter B × Vec B)']}
direct={names[0]:call_body,names[1]:[{'name':names[0],'provider':'same generated Lean file'},{'name':'loop','provider':'Aeneas.Std loop helper'}],names[2]:call_body,names[3]:[{'name':names[2],'provider':'same generated Lean file'},{'name':'loop','provider':'Aeneas.Std loop helper'}]}
blocks_meta=[]
for name in names:
 role='loop body' if name.endswith('.body') else 'loop wrapper'
 line='63:59-63:114' if 'loop0' in name else '64:59-64:114'
 key='loop0.body' if 'loop0.body' in name else 'loop0' if 'loop0' in name else 'loop1.body' if 'loop1.body' in name else 'loop1'
 blocks_meta.append({'lean_name':'AspisR292PrivateBatch.'+name,'role':role,'rust_source_span':{'file':'../r110_norm.rs','lines':line},'verbatim_block_sha256':hashlib.sha256(blocks[name].encode()).hexdigest(),'direct_calls':direct[name],'types':typed[key]})
manifest={'scope':'Read-only direct-dependency inventory of four R292-generated forward-prefix loop definitions. No Lean staging/build or semantic interpretation.','source_revision_recorded':'380c7d46c9719dcfcab601fac2607861d47dee02','frozen_source_root':'/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a (no Git metadata)','frozen_source_hashes':source_hashes,'artifact_hashes':{k:hashlib.sha256(v.read_bytes()).hexdigest() for k,v in inputs.items()},'verbatim_block_file_sha256':hashlib.sha256((out/'verbatim-blocks.lean').read_bytes()).hexdigest(),'blocks':blocks_meta,'body_alpha_equality':{'loop0_body_vs_loop1_body_after_token_boundary_renaming_px_py_and_x_y':body_eq,'method':'exact generated do-block text compared after token-boundary alpha-renaming of source-specific iterator element and vector accumulator identifiers; signatures/docs excluded'},'direct_external_template_declarations_referenced_by_four_blocks':[last],'all_r292_unresolved_external_function_templates':trres['unresolved_external_template_declarations']['functions'],'all_r292_unresolved_external_type_templates':trres['unresolved_external_template_declarations']['types'],'other_function_template_refs_in_four_blocks':[],'chain_type_template_referenced_in_four_blocks':False,'semantic_boundary':'Direct syntax/binding metadata only. No transitive helper behavior or source semantics is claimed. core.slice.Slice.last remains an external template dependency; it is not replaced or assumed.'}
(out/'inventory.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'blocks':len(blocks),'body_alpha_equal':body_eq,'verbatim_sha256':manifest['verbatim_block_file_sha256'],'inventory_sha256':hashlib.sha256((out/'inventory.json').read_bytes()).hexdigest()},indent=2))
