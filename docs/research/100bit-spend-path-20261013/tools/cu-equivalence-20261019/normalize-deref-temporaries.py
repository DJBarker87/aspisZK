#!/usr/bin/env python3
"""Experimental, guarded LLBC copy-for-deref temporary elimination.

Only an anonymous mutable-slice reference snapshot consumed once by the next
reborrow (including its metadata) is eligible. All other mutable copies remain.
This is a frontend experiment, not admission of the Rust array library.
"""
from pathlib import Path
import argparse,copy,hashlib,json

def decode_hashcons(value,memo):
    if isinstance(value,list):return [decode_hashcons(x,memo) for x in value]
    if not isinstance(value,dict):return value
    if set(value)=={'HashConsedValue'}:
        key,raw=value['HashConsedValue'];inner=decode_hashcons(raw,memo)
        if key in memo:assert memo[key]==inner,key
        memo[key]=inner
        return {'Untagged':copy.deepcopy(inner)}
    if set(value)=={'Deduplicated'}:
        return {'Untagged':copy.deepcopy(memo[value['Deduplicated']])}
    return {k:decode_hashcons(v,memo) for k,v in value.items()}

def unbox(value):
    while isinstance(value,dict) and set(value)=={'Untagged'}:value=value['Untagged']
    return value

def erased_type(value):
    value=unbox(value)
    if isinstance(value,list):return [erased_type(x) for x in value]
    if not isinstance(value,dict):return value
    if set(value)=={'Ref'}:
        _,target,kind=value['Ref']
        return {'Ref':[None,erased_type(target),kind]}
    return {k:([None for _ in v] if k=='regions' else erased_type(v)) for k,v in value.items()}

def mutable_slice(ty):
    ty=unbox(ty)
    if not isinstance(ty,dict) or set(ty)!={'Ref'}:return False
    _,target,kind=ty['Ref'];target=unbox(target)
    return kind=='Mut' and isinstance(target,dict) and set(target)=={'Slice'}

def local_place(value):
    if isinstance(value,dict) and 'ty' in value and isinstance(value.get('kind'),dict):
        kind=value['kind']
        if set(kind)=={'Local'}:return kind['Local']
    return None

def local_occurrences(value,local):
    count=int(local_place(value)==local)
    if isinstance(value,dict):return count+sum(local_occurrences(v,local) for v in value.values())
    if isinstance(value,list):return count+sum(local_occurrences(v,local) for v in value)
    return count

def local_ids(value):
    found=set();n=local_place(value)
    if n is not None:found.add(n)
    if isinstance(value,dict):
        for v in value.values():found.update(local_ids(v))
    elif isinstance(value,list):
        for v in value:found.update(local_ids(v))
    return found

def blocks(value,path=()):
    if isinstance(value,dict):
        if isinstance(value.get('statements'),list):yield path,value
        for key,item in value.items():yield from blocks(item,path+(key,))
    elif isinstance(value,list):
        for i,item in enumerate(value):yield from blocks(item,path+(i,))

def projection_of(place,local,projection):
    if not isinstance(place,dict):return False
    parts=place.get('kind',{}).get('Projection')
    return isinstance(parts,list) and len(parts)==2 and local_place(parts[0])==local and parts[1]==projection

def normalize(document):
    assert document['charon_version']=='0.1.223'
    assert document['has_errors'] is False
    options=document['translated']['options']
    assert not options['skip_borrowck'] and not options['no_typecheck']
    memo={};result=decode_hashcons(document,memo);changes=[];rejected=[]
    for function in result['translated']['fun_decls']:
        if function is None:continue
        entry=function.get('body')
        body=entry.get('Structured') if isinstance(entry,dict) else None
        if body is None:continue
        locals_=body['locals']['locals'];arg_count=body['locals']['arg_count']
        for path,block in list(blocks(body['body'])):
            statements=block['statements']
            for i,statement in enumerate(statements):
                assignment=statement.get('kind',{}).get('Assign') if isinstance(statement.get('kind'),dict) else None
                if not assignment:continue
                dest,rvalue=assignment;temp=local_place(dest)
                use=rvalue.get('Use')
                if temp is None or not use or len(use)!=2 or use[1]!='No':continue
                source=use[0].get('Copy')
                if source is None or not mutable_slice(source['ty']):continue
                reason=None
                if temp<=arg_count or locals_[temp]['name'] is not None:reason='destination is not an anonymous temporary'
                elif not mutable_slice(dest['ty']) or erased_type(dest['ty'])!=erased_type(source['ty']):reason='reference type mismatch'
                elif temp in local_ids(source):reason='self-dependent source'
                j=i+1;protected=local_ids(source)|{temp}
                while reason is None and j<len(statements):
                    kind=statements[j]['kind']
                    if not isinstance(kind,dict) or len(kind)!=1:break
                    op,arg=next(iter(kind.items()))
                    if op not in {'StorageLive','StorageDead'}:break
                    if arg in protected:reason='intervening storage change to snapshot/source';break
                    j+=1
                borrow=None
                if reason is None and j<len(statements):
                    next_assignment=statements[j]['kind'].get('Assign') if isinstance(statements[j]['kind'],dict) else None
                    if next_assignment and local_place(next_assignment[0])!=temp:
                        borrow=next_assignment[1].get('Ref')
                if reason is None and (not borrow or borrow['kind'] not in {'Shared','Mut','TwoPhaseMut'}):reason='next semantic statement is not a reborrow'
                if reason is None and not projection_of(borrow['place'],temp,'Deref'):reason='reborrow does not dereference only the snapshot'
                metadata=borrow.get('ptr_metadata',{}).get('Copy') if borrow else None
                if reason is None and not projection_of(metadata,temp,'PtrMetadata'):reason='metadata is not read from the same snapshot'
                if reason is None and local_occurrences(body['body'],temp)!=3:reason='snapshot has an additional semantic use'
                if reason:
                    rejected.append(dict(function=function['def_id'],statement=statement['id'],temporary=temp,reason=reason));continue
                before=copy.deepcopy(statements[j])
                borrow['place']['kind']['Projection'][0]=copy.deepcopy(source)
                metadata['kind']['Projection'][0]=copy.deepcopy(source)
                statement['kind']='Nop'
                assert local_occurrences(body['body'],temp)==0
                changes.append(dict(function=function['def_id'],block=list(path),copy_statement=statement['id'],
                    borrow_statement=statements[j]['id'],temporary=temp,source_place=source,
                    erased_types_equal=True,semantic_uses_before=3,semantic_uses_after=0,
                    borrow_before=before,borrow_after=copy.deepcopy(statements[j])))
    return result,dict(status='EXPERIMENTAL_NORMALIZATION_NOT_LIBRARY_ADMISSION',
        schema='charon-0.1.223',hashcons_values_expanded=len(memo),changes=changes,rejected=rejected,
        guards=['anonymous local beyond arguments','same mutable-slice type modulo regions',
          'no self-dependent source','only unrelated storage markers before next reborrow',
          'exact dereference and metadata of the same snapshot','no additional semantic use anywhere in function'],
        rust_source_bodies_or_signatures_edited=False,llbc_bodies_rewritten=bool(changes),
        ordinary_mutable_copy_check_disabled=False)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('output',type=Path)
    ap.add_argument('--report',required=True,type=Path);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    raw=args.input.read_bytes();document=json.loads(raw);result,report=normalize(document)
    output=(json.dumps(result,separators=(',',':'))+'\n').encode()
    report.update(input_sha256=hashlib.sha256(raw).hexdigest(),output_sha256=hashlib.sha256(output).hexdigest(),
        normalizer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    encoded=(json.dumps(report,indent=2)+'\n').encode()
    if args.check:assert args.output.read_bytes()==output;assert args.report.read_bytes()==encoded
    else:
        assert not args.output.exists() and not args.report.exists()
        args.output.write_bytes(output);args.report.write_bytes(encoded)
    print(json.dumps(dict(status=report['status'],changes=len(report['changes']),rejected=len(report['rejected']),check=args.check)))

if __name__=='__main__':main()
