import hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parent
p=ROOT/'R281PrivateFieldLeaves.llbc'; raw=p.read_bytes(); artifact=json.loads(raw); d=artifact['translated']
# Decode hash-consed references for the associated impl's receiver type.
h={}
def collect(x):
    if isinstance(x,dict):
        if 'HashConsedValue' in x:
            i,v=x['HashConsedValue'];h[i]=v
        for v in x.values():collect(v)
    elif isinstance(x,list):
        for v in x:collect(v)
collect(artifact)
def decode(x,seen=()):
    if isinstance(x,dict):
        if 'HashConsedValue' in x:
            i,v=x['HashConsedValue'];assert i not in seen;return decode(v,seen+(i,))
        if 'Deduplicated' in x:
            i=x['Deduplicated'];assert i in h and i not in seen;return decode(h[i],seen+(i,))
        return {k:decode(v,seen) for k,v in x.items()}
    if isinstance(x,list):return[decode(v,seen)for v in x]
    return x
files={f['id']:str(f['name'].get('Local','')) for f in d['files'] if isinstance(f,dict)}
field_ids={i for i,n in files.items() if n.endswith('/crates/aspis-core/src/field.rs')}
types={t['def_id']:t for t in d['type_decls'] if isinstance(t,dict)}
def ident_tail(name):return name[-1].get('Ident',[None])[0] if name and isinstance(name[-1],dict) and 'Ident' in name[-1] else None
expected={'neg':874,'mul_m31':927}; found={}
for method,line in expected.items():
    rows=[]
    for f in d['fun_decls']:
        meta=f.get('item_meta') or {}; span=meta.get('span',{}).get('data',{})
        if ident_tail(meta.get('name'))==method and span.get('file_id') in field_ids and span.get('beg',{}).get('line')==line:
            name=decode(meta['name']); impl=name[-2]['Impl']['Ty']['skip_binder']; assert impl=={'Adt':{'id':{'Adt':0},'generics':{'regions':[],'types':[],'const_generics':[],'trait_refs':[]}}},(method,impl)
            assert types[0]['item_meta']['name'][-1]['Ident'][0]=='QM31'
            rows.append({'fun_id':f['def_id'],'method':method,'source_file':files[span['file_id']],'source_line':line,'body_kind':'Structured' if isinstance(f.get('body'),dict) and 'Structured' in f['body'] else str(f.get('body')),'item_meta_is_local':meta.get('is_local'),'receiver_type':'aspis_core::field::QM31','body_sha256':hashlib.sha256(json.dumps(decode(f['body']),sort_keys=True,separators=(',',':')).encode()).hexdigest()})
    assert len(rows)==1, (method,rows)
    found[method]=rows[0]
assert artifact.get('has_errors') is False
assert all(x['body_kind']=='Structured' and x['item_meta_is_local'] is False for x in found.values())
inspection={'artifact_sha256':hashlib.sha256(raw).hexdigest(),'has_errors':artifact.get('has_errors'),'selected_roots':found,'root_body_presence':'both requested methods have structured bodies at the exact frozen field.rs lines; Charon item_meta.is_local is false because these are in the aspis_core dependency crate','frozen_source_hash':json.load(open(ROOT/'extract-command.json'))['verified_source_hashes']['aspis_core_field.rs'],'source_revision_recorded':json.load(open(ROOT/'extract-command.json'))['source_revision_recorded'],'translation_run':False}
(ROOT/'root-body-inspection.json').write_text(json.dumps(inspection,indent=2)+'\n')
acceptance={'accepted_for_further_structural_review':True,'has_errors':False,'method_body_presence_verified':True,'external_root_justification':'The two exact roots are source methods in the frozen aspis_core dependency (field.rs SHA recorded in extract-command.json); Charon reports is_local=false for those external-crate items while still emitting each exact selected method as a Structured body. This acceptance is only structural LLBC review, not source semantics or proof evidence.','selected_roots':found,'preserved_initial_strict_local_check':'rejected-preflight-check.json','translation_run':False}
(ROOT/'acceptance.json').write_text(json.dumps(acceptance,indent=2)+'\n')
print(json.dumps({'artifact_sha256':inspection['artifact_sha256'],'has_errors':False,'roots':{k:{'FunId':v['fun_id'],'line':v['source_line'],'body':v['body_kind'],'is_local':v['item_meta_is_local']} for k,v in found.items()}},indent=2))
