#!/usr/bin/env python3
"""Mechanical inventory of Charon LLBC/Aeneas output. No semantic proof."""
import collections, hashlib, json, re, sys
from pathlib import Path
if len(sys.argv)!=3: raise SystemExit('usage: audit-terminal-translation.py <Terminal-name-adapt.llbc> <generated-dir>')
llbc=Path(sys.argv[1]); gen=Path(sys.argv[2]); raw=json.loads(llbc.read_text()); tr=raw['translated']; funcs=[x for x in tr['fun_decls'] if x is not None]
def body_kind(x): return next(iter(x['body'])) if x.get('body') else None
def nameparts(x):
    return [it['Ident'][0] if isinstance(it,dict) and 'Ident' in it else str(it) for it in x.get('item_meta',{}).get('name',[])]
def typename(x): return '::'.join(nameparts(x))
fun_counts=collections.Counter((x.get('item_meta',{}).get('is_local'),x.get('item_meta',{}).get('opacity'),body_kind(x)) for x in funcs)
target_names=['aspis_r1_mask_extraction_probe::extraction_probe::terminal_qm31_probe','aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::terminal_parts','aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts']
def formatted(x):
    m=x['item_meta']; sp=m['span']['data']; name=typename(x)
    file_id=sp.get('file_id')
    return {'name':name,'source_file':tr['files'][file_id]['name'].get('Local') if file_id is not None else None,'local':m['is_local'],'opacity':m['opacity'],'body_kind':body_kind(x),'span':sp}
# Some Charon source file paths are encoded at src.file_id; retain names/spans and target metadata regardless.
targets=[]
for f in funcs:
    nm=typename(f)
    if any(nm==n or nm.endswith(n.split('::',1)[-1]) for n in target_names) or ('terminal_qm31' in nm and 'call_once' not in nm and 'call_mut' not in nm):
        targets.append(formatted(f))
field_types=[]
for t in tr['type_decls']:
 if t is None: continue
 nm=typename(t)
 if any(q in nm for q in ('field::M31','field::CM31','field::QM31','field::PreparedQm31Multiplier')):
  m=t['item_meta']; field_types.append({'name':nm,'source_span':m['span']['data'],'local':m['is_local'],'opacity':m['opacity']})
external_file=gen/'AspisR1SelectedMaskProbe'/'FunsExternal_Template.lean'
external_text=external_file.read_text(); axioms=re.findall(r'(?m)^axiom\s+([^\s(:]+)',external_text)
translation=json.loads((gen/'translation.json').read_text())
res={'scope':'mechanical LLBC/Aeneas output inventory; no Lean compilation or source-equivalence claim','llbc_sha256':hashlib.sha256(llbc.read_bytes()).hexdigest(),'llbc_bytes':llbc.stat().st_size,'charon_version':raw.get('charon_version'),'has_errors':raw.get('has_errors'),'llbc_function_slots':len(tr['fun_decls']),'llbc_non_null_functions':len(funcs),'llbc_type_decls':len(tr['type_decls']),'llbc_ordered_decls':len(tr['ordered_decls']),'all_non_null_function_records_have_body':all(x.get('body') is not None for x in funcs),'function_body_categories':[{ 'is_local':k[0],'opacity':k[1],'body_kind':k[2],'count':v} for k,v in sorted(fun_counts.items(),key=lambda z:str(z[0]))],'generated_local_transparent_structured_count':fun_counts[(True,'Transparent','Structured')],'opaque_or_nonlocal_count':sum(v for k,v in fun_counts.items() if k[0] is not True or k[1] != 'Transparent'),'target_functions':targets,'field_types':field_types,'translation_counts':{'functions':len(translation.get('functions',[])),'types':len(translation.get('types',[])),'trait_impls':len(translation.get('trait_impls',[]))},'external_template_axiom_count':len(axioms),'external_template_axioms':axioms,'from_fn_external_axiom_present':any(x.endswith('from_fn') for x in axioms),'copy_helper_local_definition_present':'def array_from_fn_copy' in (gen/'AspisR1SelectedMaskProbe'/'Funs.lean').read_text(),'generated_file_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((gen/'AspisR1SelectedMaskProbe').glob('*.lean'))}}
Path('/tmp/output-audit.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({'llbc_function_slots':res['llbc_function_slots'],'llbc_non_null_functions':res['llbc_non_null_functions'],'function_body_categories':res['function_body_categories'],'translation_counts':res['translation_counts'],'external_template_axiom_count':res['external_template_axiom_count']},indent=2))
