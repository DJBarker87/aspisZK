import copy, hashlib, json, pathlib, sys
src,dst,receipt=map(pathlib.Path,sys.argv[1:])
data=json.loads(src.read_text()); translated=data['translated']
leaf=lambda x: x['item_meta']['name'][-1].get('Ident',[None])[0]
types=[(i,t) for i,t in enumerate(translated['type_decls']) if t and leaf(t)=='M31' and t['item_meta'].get('source_text')=='pub struct M31(pub u32);']
assert len(types)==1, f'M31 type candidates={len(types)}'
ti,t=types[0]; span=t['item_meta']['span']
funs=[(i,f) for i,f in enumerate(translated['fun_decls']) if f and leaf(f)=='M31' and f['item_meta'].get('source_text')=='pub struct M31(pub u32);' and f['item_meta'].get('span')==span]
assert len(funs)==1, f'M31 constructor candidates={len(funs)}'
fi,f=funs[0]
assert f['item_meta']['attr_info'].get('rename') is None
f['item_meta']['attr_info']['rename']='M31_constructor'
dst.write_text(json.dumps(data,separators=(',',':')))
reverse=copy.deepcopy(data); reverse['translated']['fun_decls'][fi]['item_meta']['attr_info']['rename']=None
assert reverse==json.loads(src.read_text()), 'metadata edit changed more than one path'
h=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
receipt.write_text(json.dumps({'kind':'v4 one-field metadata alpha rename (same as terminal-qm31-fromfn-copy-candidate-v4-aeneas-20261019 run script)','raw_llbc_sha256':h(src),'adapted_llbc_sha256':h(dst),'only_changed_path':f'translated.fun_decls[{fi}].item_meta.attr_info.rename','deep_reverse_transform_equal':True},indent=1))
