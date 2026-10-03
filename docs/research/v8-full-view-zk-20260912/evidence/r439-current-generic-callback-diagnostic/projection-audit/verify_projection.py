#!/usr/bin/env python3
"""Independent byte-level and AST-structure audit for the R439 group projection."""
import argparse, hashlib, json, pathlib

HERE = pathlib.Path(__file__).resolve().parent
PROJ_DIR = HERE.parent / 'lead-projection-a'
DEFAULT_SOURCE = HERE.parent / 'body-comparison' / 'input' / 'R438GenericClosureDispatch.llbc'
DEFAULT_TARGET = PROJ_DIR / 'R439GenericGammaSelection.llbc'
EXPECTED_SOURCE_SHA = '76eefed780e23eb3243413b913e935dc7a9b661bceeb0fc0346668621ab07fb6'
EXPECTED_TARGET_SHA = 'd28419f408e6bab79c80859db37e137f4ab62b6bd73c7c5a5d909582308a75b9'
EXPECTED_GENERATOR_SHA = '602d5b5d96a54c50b7b4bbacee6effc5927556eb90abbefbc05bac674691791c'
EXPECTED_ROOT_GROUPS = {('Fun',284),('TraitImpl',47)}


def sha(b): return hashlib.sha256(b).hexdigest()

def array_value_span(raw, key):
    token = ('"' + key + '":').encode()
    at = raw.find(token)
    assert at >= 0 and raw.find(token, at + 1) < 0, f'expected one {key} key'
    start = at + len(token)
    while raw[start:start+1] in b' \t\r\n': start += 1
    assert raw[start:start+1] == b'[', f'{key} must be an array'
    depth = 0; in_string = False; escaped = False
    for i in range(start, len(raw)):
        c = raw[i]
        if in_string:
            if escaped: escaped = False
            elif c == 0x5c: escaped = True
            elif c == 0x22: in_string = False
            continue
        if c == 0x22: in_string = True
        elif c == 0x5b: depth += 1
        elif c == 0x5d:
            depth -= 1
            if depth == 0: return start, i + 1
    raise AssertionError(f'unclosed {key} array')

def ordered_item(v):
    assert isinstance(v,dict) and len(v)==1, v
    k,val=next(iter(v.items()))
    if isinstance(val,dict) and set(val)=={'NonRec'}:
        return (k,val['NonRec'])
    if isinstance(val,dict) and set(val)=={'Rec'}:
        return (k,tuple(val['Rec']))
    raise AssertionError(('unexpected ordered declaration encoding',v))

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--source',type=pathlib.Path,default=DEFAULT_SOURCE)
    ap.add_argument('--target',type=pathlib.Path,default=DEFAULT_TARGET)
    ap.add_argument('--out',type=pathlib.Path,default=HERE/'audit-report.json')
    a=ap.parse_args(); src=a.source.read_bytes(); dst=a.target.read_bytes()
    source_sha=sha(src); target_sha=sha(dst)
    assert source_sha==EXPECTED_SOURCE_SHA,(source_sha,EXPECTED_SOURCE_SHA)
    assert target_sha==EXPECTED_TARGET_SHA,(target_sha,EXPECTED_TARGET_SHA)
    src_obj=json.loads(src); dst_obj=json.loads(dst)
    assert src_obj.get('has_errors') is False and dst_obj.get('has_errors') is False
    src_t=src_obj['translated']; dst_t=dst_obj['translated']
    s0,s1=array_value_span(src,b'ordered_decls'.decode())
    t0,t1=array_value_span(dst,b'ordered_decls'.decode())
    assert src[:s0]==dst[:t0], 'raw prefix through ordered_decls value changed'
    assert src[s1:]==dst[t1:], 'raw suffix after ordered_decls value changed'
    src_other=dict(src_t); dst_other=dict(dst_t)
    src_order=src_other.pop('ordered_decls'); dst_order=dst_other.pop('ordered_decls')
    assert src_other==dst_other, 'decoded translated fields other than ordered_decls differ'
    root=dst_t['fun_decls'][284]
    root_source=root['src']['TraitImpl']
    assert root_source['impl_ref']['id']==47
    assert root_source['trait_ref']['id']==9
    assert root_source['item_id']=={'Method':0} and root_source['reuses_default'] is False
    impl=dst_t['trait_impls'][47]
    assert impl['impl_trait']['id']==9
    src_members=[ordered_item(x) for x in src_order]
    dst_members=[ordered_item(x) for x in dst_order]
    receipt=json.loads((PROJ_DIR/'projection-receipt.json').read_text())
    assert len(src_members)==310 and len(set(src_members))==len(src_members)
    assert len(dst_members)==40 and len(set(dst_members))==len(dst_members)
    selected=set(dst_members)
    assert EXPECTED_ROOT_GROUPS<=selected
    assert selected=={tuple(x) for x in receipt['selected_members']}
    subsequence=[m for m in src_members if m in selected]
    assert dst_members==subsequence, 'projection reordered or changed retained declaration groups'
    assert all(m in set(src_members) for m in dst_members)
    assert sum(1 for m in dst_members if m[0]=='Fun')==27
    assert sum(1 for m in dst_members if m[0]=='Global')==3
    assert sum(1 for m in dst_members if m[0]=='TraitDecl')==2
    assert sum(1 for m in dst_members if m[0]=='TraitImpl')==2
    assert sum(1 for m in dst_members if m[0]=='Type')==6
    for field in ('fun_decls','type_decls','trait_decls','trait_impls','global_decls','trait_decls_groups','trait_impls_groups'):
        if field in src_t: assert src_t[field]==dst_t[field],field
    assert receipt['source_sha256']==source_sha and receipt['target_sha256']==target_sha
    generator=PROJ_DIR/'project_groups.py'; gen_sha=sha(generator.read_bytes())
    assert gen_sha==EXPECTED_GENERATOR_SHA,(gen_sha,EXPECTED_GENERATOR_SHA)
    report={
      'status':'PASS',
      'scope':'Independent mechanical projection audit only; not a translation, execution, lifetime, or semantic-correctness claim.',
      'source_path':str(a.source),'source_sha256':source_sha,'source_size_bytes':len(src),
      'target_path':str(a.target),'target_sha256':target_sha,'target_size_bytes':len(dst),
      'projection_generator_sha256':gen_sha,'receipt_sha256':sha((PROJ_DIR/'projection-receipt.json').read_bytes()),
      'raw_json_change_boundary':{'only_field':'translated.ordered_decls','source_array_span':[s0,s1],'target_array_span':[t0,t1],'identical_prefix_bytes':s0,'identical_suffix_bytes':len(src)-s1,'source_prefix_sha256':sha(src[:s0]),'target_prefix_sha256':sha(dst[:t0]),'source_suffix_sha256':sha(src[s1:]),'target_suffix_sha256':sha(dst[t1:]),'all_other_raw_bytes_identical':True},
      'ordered_declarations':{'source_count':len(src_order),'target_count':len(dst_order),'target_exact_order_preserving_subsequence':True,'target_group_counts':{'Fun':27,'Global':3,'TraitDecl':2,'TraitImpl':2,'Type':6},'target_groups':[[k,v] for k,v in dst_members]},
      'root_binding':{'fun_id':284,'source_impl_id':47,'source_trait_id':9,'source_method_id':0,'reuses_default':False,'impl47_trait_id':9,'both_root_groups_selected':True},
      'all_other_translated_json_values_equal':True,
      'full_declaration_tables_and_hashcons_records_preserved_byte_for_byte':True,
      'limitations':['This checks JSON bytes and selection structure only. It does not establish source execution, callback behavior, or cryptographic/security properties.']
    }
    a.out.parent.mkdir(parents=True,exist_ok=True); a.out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','source_sha256':source_sha,'target_sha256':target_sha,'selected_groups':len(dst_order),'identical_prefix_bytes':s0,'identical_suffix_bytes':len(src)-s1,'all_other_raw_bytes_identical':True,'root_fun284_impl47':True,'out':str(a.out)},indent=2))
if __name__=='__main__': main()
