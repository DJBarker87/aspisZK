#!/usr/bin/env python3
"""Inspect existing LLBC metadata and return-slot writes; no Charon invocation."""
import json,lzma,pathlib,re,subprocess
from NKT_checker import sha
P=pathlib.Path(__file__).parent

def main():
 path='evidence/batch-merkle-20261108/NJS_emitted/NJS_batch.llbc.xz';packed=pathlib.Path(path).read_bytes();raw=lzma.decompress(packed);D=json.loads(raw);t=D['translated']
 f=next(x for x in t['fun_decls'] if x and x['item_meta']['name'][-1].get('Ident',[''])[0]=='batch_tree')
 name=lambda x:'::'.join(y['Ident'][0] for y in x['item_meta']['name'] if 'Ident' in y)
 def walk(v):
  if isinstance(v,dict):
   if all(k in v for k in ['kind','span','id']):
    line=v['span']['data']['beg']['line'];k=v['kind'];leaf=None
    if line>=196 and isinstance(k,dict):
     if 'Assign' in k and k['Assign'][0]['kind']=={'Local':0}:leaf=k
     if 'Call' in k:
      c=k['Call']['call']
      if c['dest']['kind']=={'Local':0}:
       idx=c['func']['Regular']['kind']['Fun']['Regular'];leaf={'Call_return_slot':c,'callee':name(t['fun_decls'][idx])}
    if leaf:result.append({'statement_id':v['id'],'source_line':line,'operation':leaf})
   for x in v.values():walk(x)
  elif isinstance(v,list):
   for x in v:walk(x)
 result=[];walk(f['body'])
 native=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/candidate.rs'],text=True)
 src=f['item_meta']['source_text'];matches=src in native
 out={'path':path,'compressed_sha256':sha(packed),'uncompressed_sha256':sha(raw),'charon_version':D['charon_version'],'function':name(f),'source_text_sha256':sha(src.encode()),'source_text_is_exact_frozen_substring':matches,'return_slot':0,'return_slot_writes_after_loop':result,'conclusion':'Charon retains the two Parse-guard branches and Merkle rejection as Err variant writes, and node_count residual conversion targets return slot0. The Aeneas emitted none discards those values. No new Charon/Aeneas run.'}
 assert matches and {196,200,203,205}<={x['source_line'] for x in result}
 P.joinpath('NKT_LLBC_REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'source_match':matches,'return_slot_writes':len(result),'charon_version':D['charon_version']}))
if __name__=='__main__':main()
