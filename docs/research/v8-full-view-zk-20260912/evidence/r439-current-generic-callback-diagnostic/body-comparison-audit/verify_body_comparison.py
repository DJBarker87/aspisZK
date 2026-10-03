#!/usr/bin/env python3
"""Independent structural audit of the saved R437 Fun112 / R438 Fun284 comparison."""
import argparse, collections, hashlib, json
from pathlib import Path

DEFAULT=Path(__file__).resolve().parents[1]/'body-comparison'
IDMAP={'fun':{24:20,112:284,124:321},'type':{50:65},'trait_decl':{3:9},'trait_impl':{35:47},'adt':{50:65}}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def canonjson(x): return json.dumps(x,sort_keys=True,separators=(',',':'))
def hashcons_map(t):
    hc={}
    def walk(x):
        if isinstance(x,dict):
            if set(x)=={'HashConsedValue'}:
                q=x['HashConsedValue']; assert isinstance(q,list) and len(q)==2 and isinstance(q[0],int)
                assert q[0] not in hc or hc[q[0]]==q[1], f'conflicting hashcons {q[0]}'
                hc[q[0]]=q[1]
            for v in x.values(): walk(v)
        elif isinstance(x,list):
            for v in x: walk(v)
    walk(t); return hc
def expand(x,hc,active=()):
    if isinstance(x,dict):
        if set(x)=={'HashConsedValue'}: return expand(x['HashConsedValue'][1],hc,active)
        if set(x)=={'Deduplicated'}:
            i=x['Deduplicated']; assert i in hc, f'missing hashcons {i}'
            assert i not in active, f'hashcons cycle {active+(i,)}'
            return expand(hc[i],hc,active+(i,))
        return {k:expand(v,hc,active) for k,v in x.items()}
    if isinstance(x,list): return [expand(v,hc,active) for v in x]
    return x
def statement_envelope(x): return isinstance(x,dict) and all(k in x for k in ('span','id','kind','comments_before'))
def normalize(x,path=(),parent=None,edits=None):
    if edits is None: edits=[]
    if isinstance(x,dict):
        out={}; isstmt=statement_envelope(x)
        for k,v0 in x.items():
            if k=='span': continue
            if isstmt and k=='id': continue
            v=v0
            if k=='def_id' and path==() and isinstance(v,int) and v in IDMAP['fun']:
                nv=IDMAP['fun'][v]; edits.append({'path':list(path+(k,)),'domain':'function-declaration','old':v,'new':nv}); v=nv
            if k=='Regular' and parent=='Fun' and isinstance(v,int) and v in IDMAP['fun']:
                nv=IDMAP['fun'][v]; edits.append({'path':list(path+(k,)),'domain':'function-reference','old':v,'new':nv}); v=nv
            if k=='id' and isinstance(v,dict) and set(v)=={'Adt'} and isinstance(v['Adt'],int) and v['Adt'] in IDMAP['adt']:
                nv=IDMAP['adt'][v['Adt']]; edits.append({'path':list(path+(k,'Adt')),'domain':'adt-reference','old':v['Adt'],'new':nv}); v={'Adt':nv}
            if k=='Adt' and isinstance(v,list) and v and isinstance(v[0],int) and v[0] in IDMAP['adt']:
                nv=IDMAP['adt'][v[0]]; edits.append({'path':list(path+(k,0)),'domain':'adt-reference','old':v[0],'new':nv}); v=[nv,*v[1:]]
            if k=='TraitImpl' and isinstance(v,dict) and isinstance(v.get('id'),int) and v['id'] in IDMAP['trait_impl']:
                vv=dict(v); old=vv['id']; vv['id']=IDMAP['trait_impl'][old]; edits.append({'path':list(path+(k,'id')),'domain':'trait-impl-reference','old':old,'new':vv['id']}); v=vv
            if k=='Trait' and isinstance(v,int) and v in IDMAP['trait_impl']:
                nv=IDMAP['trait_impl'][v]; edits.append({'path':list(path+(k,)),'domain':'trait-impl-name-reference','old':v,'new':nv}); v=nv
            if k=='id' and 'trait_ref' in path and isinstance(v,int) and v in IDMAP['trait_decl']:
                nv=IDMAP['trait_decl'][v]; edits.append({'path':list(path+(k,)),'domain':'trait-decl-reference','old':v,'new':nv}); v=nv
            if k=='id' and 'impl_ref' in path and isinstance(v,int) and v in IDMAP['trait_impl']:
                nv=IDMAP['trait_impl'][v]; edits.append({'path':list(path+(k,)),'domain':'trait-impl-reference','old':v,'new':nv}); v=nv
            out[k]=normalize(v,path+(k,),k,edits)
        return out
    if isinstance(x,list): return [normalize(v,path+(i,),parent,edits) for i,v in enumerate(x)]
    return x
def diffs(a,b,path=()):
    if type(a)!=type(b): return [{'path':list(path),'kind':'type','left':a,'right':b}]
    if isinstance(a,dict):
        out=[]
        for k in sorted(set(a)|set(b)):
            if k not in a: out.append({'path':list(path+(k,)),'kind':'missing_left','right':b[k]})
            elif k not in b: out.append({'path':list(path+(k,)),'kind':'missing_right','left':a[k]})
            else: out.extend(diffs(a[k],b[k],path+(k,)))
        return out
    if isinstance(a,list):
        out=[]
        if len(a)!=len(b): out.append({'path':list(path),'kind':'length','left':len(a),'right':len(b)})
        for i,(x,y) in enumerate(zip(a,b)): out.extend(diffs(x,y,path+(i,)))
        return out
    return [] if a==b else [{'path':list(path),'kind':'value','left':a,'right':b}]
def last_name(path):
    return path[-1]['Ident'][0] if isinstance(path,list) and path and isinstance(path[-1],dict) and 'Ident' in path[-1] else None
def body_stats(row):
    lists=[]; unw=[]; ops=collections.Counter(); regs=[]
    def visit(x,path=()):
        if isinstance(x,dict):
            if isinstance(x.get('statements'),list): lists.append({'path':list(path+('statements',)),'count':len(x['statements'])})
            if 'on_unwind' in x: unw.append(list(path+('on_unwind',)))
            if isinstance(x.get('kind'),dict) and len(x['kind'])==1: ops[next(iter(x['kind']))]+=1
            if set(x)=={'Var'} and isinstance(x['Var'],dict): regs.append({'path':list(path),'value':x['Var']})
            for k,v in x.items(): visit(v,path+(k,))
        elif isinstance(x,list):
            for i,v in enumerate(x): visit(v,path+(i,))
    visit(row)
    return {'statement_lists':lists,'total_statements':sum(r['count'] for r in lists),'unwinds':unw,'operations':dict(ops),'regions':regs}
def run(comp,out):
    comp=Path(comp); out=Path(out); a_path=comp/'input/R437PointerWrapperLayout.llbc'; b_path=comp/'input/R438GenericClosureDispatch.llbc'
    a=json.loads(a_path.read_text()); b=json.loads(b_path.read_text()); ta=a['translated']; tb=b['translated']
    assert a['has_errors'] is False and b['has_errors'] is False
    assert (sha(a_path),sha(b_path))==('bafe9c1297a8ea92eaea3c37c685da3f5d3fe2e04c335ac9f1f4d64c4312386c','76eefed780e23eb3243413b913e935dc7a9b661bceeb0fc0346668621ab07fb6')
    callback_a=hashlib.sha256(ta['files'][0]['contents'].encode()).hexdigest(); callback_b=hashlib.sha256(tb['files'][0]['contents'].encode()).hexdigest()
    assert callback_a==callback_b=='4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f'
    fa=expand(ta['fun_decls'][112],hashcons_map(ta)); fb=expand(tb['fun_decls'][284],hashcons_map(tb))
    saved=json.loads((comp/'raw-and-expanded-fun112-fun284.json').read_text())
    assert saved['raw']['R437_Fun112']==ta['fun_decls'][112] and saved['raw']['R438_Fun284']==tb['fun_decls'][284]
    assert saved['expanded']['R437_Fun112']==fa and saved['expanded']['R438_Fun284']==fb
    # Type identity and operation signatures are resolved from each capture's own hash-cons table.
    resolved=[]
    for label,t,hc,ids in [('R437',ta,hashcons_map(ta),{'mul':24,'add':124}),('R438',tb,hashcons_map(tb),{'mul':20,'add':321})]:
        q=t['type_decls'][2]; qname=expand(q['item_meta']['name'],hc)
        assert last_name(qname)=='QM31'
        opfacts={}
        for op,fid in ids.items():
            f=t['fun_decls'][fid]; name=expand(f['item_meta']['name'],hc); sig=expand(f['signature'],hc)
            assert last_name(name)==op and name[0]['Ident'][0]=='aspis_core' and name[1]['Ident'][0]=='field'
            assert name[2]['Impl']['Ty']['skip_binder']['Adt']['id']['Adt']==2
            qtype={'Adt':{'generics':{'const_generics':[],'regions':[],'trait_refs':[],'types':[]},'id':{'Adt':2}}}
            assert sig['inputs']==[qtype,qtype] and sig['output']==qtype
            opfacts[op]={'fun_id':fid,'name':name,'inputs':sig['inputs'],'output':sig['output']}
        resolved.append({'capture':label,'type2_name':qname,'operations':opfacts})
    assert fa['src']['TraitImpl']['impl_ref']['id']==35 and fa['src']['TraitImpl']['trait_ref']['id']==3 and fa['src']['TraitImpl']['item_id']=={'Method':0} and fa['src']['TraitImpl']['reuses_default'] is False
    assert fb['src']['TraitImpl']['impl_ref']['id']==47 and fb['src']['TraitImpl']['trait_ref']['id']==9 and fb['src']['TraitImpl']['item_id']=={'Method':0} and fb['src']['TraitImpl']['reuses_default'] is False
    # Nominal renaming is applied explicitly to recognized ID-bearing reference fields only.
    edits=[]; ca=normalize(fa,edits=edits); cb=normalize(fb,edits=[])
    views=json.loads((comp/'canonical-structural-views.json').read_text())
    assert views['id_mapping']=={k:{str(i):j for i,j in v.items()} for k,v in IDMAP.items()} and views['R437_Fun112']==ca and views['R438_Fun284']==cb
    assert all(e['domain'] in {'function-declaration','function-reference','adt-reference','trait-impl-reference','trait-impl-name-reference','trait-decl-reference'} for e in edits)
    # The normalized comparison retains a single extra generic type argument, not a region or operation change.
    d=diffs(ca,cb)
    expected_path=['src','TraitImpl','trait_ref','generics','types']
    assert len(d)==1 and d[0]['path']==expected_path and d[0]['kind']=='length' and (d[0]['left'],d[0]['right'])==(2,3)
    extra=cb['src']['TraitImpl']['trait_ref']['generics']['types'][2]
    qtype={'Adt':{'generics':{'const_generics':[],'regions':[],'trait_refs':[],'types':[]},'id':{'Adt':2}}}
    assert extra==qtype
    saved_diff=json.loads((comp/'structural-diff.json').read_text())
    assert saved_diff['diff_count']==1 and saved_diff['diffs']==d and saved_diff['equal_after_named_id_mapping_and_span_statement_id_omission'] is False
    sa,sb=body_stats(ca),body_stats(cb)
    assert sa['statement_lists']==sb['statement_lists'] and sa['total_statements']==sb['total_statements']==51
    assert len(sa['unwinds'])==len(sb['unwinds'])==3 and sa['unwinds']==sb['unwinds']
    assert sa['operations']==sb['operations']
    assert len(sa['regions'])==len(sb['regions'])==31 and sa['regions']==sb['regions']
    assert all('Free' in r['value'] for r in sa['regions'])
    original_shape=json.loads((comp/'body-shape-audit.json').read_text())
    for side,calc in [('R437_Fun112',sa),('R438_Fun284',sb)]:
        old=original_shape[side]
        assert old['total_statements']==calc['total_statements'] and old['region_annotation_count']==len(calc['regions'])
        assert old['on_unwind_paths']==calc['unwinds'] and old['region_annotations']==calc['regions']
        assert old['operation_kind_counts']==calc['operations']
    report={'status':'PASS','inputs':{'R437_llbc_sha256':sha(a_path),'R438_llbc_sha256':sha(b_path),'callback_source_sha256_R437':callback_a,'callback_source_sha256_R438':callback_b,'has_errors_R437':a['has_errors'],'has_errors_R438':b['has_errors']},'selected_rows':{'R437_fun_id':112,'R438_fun_id':284,'raw_and_expanded_rows_match_captures':True,'R437_impl_trait_method_default':{'impl':35,'trait':3,'method':0,'reuses_default':False},'R438_impl_trait_method_default':{'impl':47,'trait':9,'method':0,'reuses_default':False}},'type_and_operations':resolved,'nominal_mapping':IDMAP,'nominal_mapping_edits':{'count':len(edits),'domains':dict(collections.Counter(e['domain'] for e in edits)),'paths_and_values':edits,'region_or_generic_fields_erased':False},'normalization_ignored_fields':['source-span fields','id fields only on recognized structured-statement envelopes'],'preserved_fields':['all 31 region annotation values and paths','generic parameter and clause fields','operation trees','all on_unwind/drop subtrees','other declaration IDs not listed in nominal_mapping_edits'],'callback_structure':{'statement_lists_R437':sa['statement_lists'],'statement_lists_R438':sb['statement_lists'],'total_statements_each':51,'unwind_paths_R437':sa['unwinds'],'unwind_paths_R438':sb['unwinds'],'unwind_count_each':3,'operation_counts_R437':sa['operations'],'operation_counts_R438':sb['operations'],'operation_counts_equal':True,'region_annotation_count_each':31,'region_annotations_R437':sa['regions'],'region_annotations_R438':sb['regions'],'region_annotation_values_and_paths_equal':True},'normalized_diff':{'count':1,'path':expected_path,'kind':'length','R437_length':2,'R438_length':3,'additional_R438_argument':extra,'additional_argument_name':'QM31 (Type2)'},'supporting_artifact_sha256':{n:sha(comp/n) for n in ['raw-and-expanded-fun112-fun284.json','canonical-structural-views.json','structural-diff.json','body-shape-audit.json','nominal-id-bijection-evidence.json','compare_bodies.py']},'boundary':'Exact native capture structure and type/signature comparison only. No source execution, borrow/alias, trait-dispatch, ABI, or semantic correspondence claim.'}
    out.mkdir(parents=True,exist_ok=True); (out/'audit-report.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    return report
if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--comparison',default=str(DEFAULT)); ap.add_argument('--out',default=str(Path(__file__).resolve().parent)); args=ap.parse_args()
    r=run(args.comparison,args.out); print(json.dumps({'status':r['status'],'input_hashes':r['inputs'],'normalized_diff':r['normalized_diff'],'statement_count':r['callback_structure']['total_statements_each'],'region_count':r['callback_structure']['region_annotation_count_each']},sort_keys=True))
