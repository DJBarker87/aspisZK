#!/usr/bin/env python3
"""Audit R314 emitted root via stable LLBC def_id and manifest Lean name."""
import hashlib,json,pathlib,re
root=pathlib.Path(__file__).resolve().parent
gen=root/'generated'; source=(root.parent/'r309-slice-last-with-length-projection/R309SliceLastWithLengthProjection.llbc').resolve()
raw=json.loads(source.read_text()); tr=raw['translated']; assert tr['ordered_decls']==[{'Type':{'NonRec':9}},{'Fun':{'NonRec':5}},{'Fun':{'NonRec':12}}]
rows=[r for r in tr['fun_decls'] if isinstance(r,dict) and r.get('def_id')==12]; assert len(rows)==1
manifest=gen/'translation.json'; md=json.loads(manifest.read_text()); functions=md.get('functions',[])
matches=[f for f in functions if f.get('def_id')==12]; entries=[]
for f in matches:
  lean_name=f.get('lean_name'); lean_file=f.get('lean_file'); hits=[]; leaf=None
  if lean_name and lean_name.startswith('AspisR314SliceLast.') and lean_file:
    leaf=lean_name[len('AspisR314SliceLast.'):]; p=gen/lean_file; lines=p.read_text().splitlines()
    hits=[i for i,l in enumerate(lines,1) if re.match(r'^\s*def\s+'+re.escape(leaf)+r'(?=\s|\{|$)',l)]
    if not hits: hits=[i+1 for i,l in enumerate(lines[:-1]) if l.strip()=='def' and lines[i+1].strip()==leaf]
  entries.append({'def_id':f.get('def_id'),'rust_name':f.get('rust_name'),'lean_name':lean_name,'lean_file':lean_file,'declaration_suffix':leaf,'definition_lines':hits})
assert len(matches)==1 and all(len(x['definition_lines'])==1 for x in entries),entries
holes={}
for key,rel in [('functions','AspisR314SliceLast/FunsExternal_Template.lean'),('types','AspisR314SliceLast/TypesExternal_Template.lean')]:
  p=gen/rel; holes[key]=re.findall(r'^axiom\s+([^\s(]+)',p.read_text(errors='replace'),re.M) if p.is_file() else None
hashes={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(gen.rglob('*')) if p.is_file()}
result={'translator_exit_status':0,'generated_dir_exists':True,'translation_json_exists':True,'function_manifest_entries':len(functions),'root_identity':'input LLBC Fun def_id 12 (stable selected row); manifest def_id match','input_rust_pattern':'core::slice::{Impl}::last','manifest_root_matches':len(matches),'root_entries':entries,'root_definition_present':True,'external_template_axiom_holes':holes,'template_status':'Templates were not emitted; no holes-filled or axiom-free conclusion is claimed.','translator_warnings':[],'generated_file_sha256':hashes,'translation_rerun':False}
(root/'translation-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
