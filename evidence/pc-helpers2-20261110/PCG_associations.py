"""Exact source-fission checks; no model output assumptions."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
norm=lambda s:re.sub(r',(?=[\]})])','',re.sub(r'\s+','',s))
def body(s,name):
 m=re.search(r'fn\s+'+name+r'\b',s);assert m,name
 start=s.index('{',m.end());depth=1;i=start+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[start:i]
source=json.loads((E/'PCG_SOURCE_MAP.json').read_text());rows={x['row']:x for x in source};results=[]
def check(row,text,transforms):
 actual=rows['POOL:'+str(row)]['body'];got=text
 for a,b in transforms:got=got.replace(a,b)
 assert norm(actual)==norm(got),(row,'fission does not erase to frozen body')
 results.append(dict(row='POOL:'+str(row),frozen_sha256=rows['POOL:'+str(row)]['frozen_body_sha256'],fission_sha256=hashlib.sha256(text.encode()).hexdigest(),transforms=transforms,exact_after_whitespace_and_optional_trailing_commas=True))
check(324,body((E/'PCG_324.rs').read_text(),'global_window'),[('parent_window','pool_v1_tree_parent'),(',log',''),('[Digest;8]','[Digest;8]')])
check(345,body((E/'PCG_345.rs').read_text(),'get_window'),[('reply_window(log)','program::get_return_data()')])
check(296,body((E/'PCG_296.rs').read_text(),'marker_window'),[('hash_window','solana_program::hash::hashv'),(',log',''),('pack_window','pack_pool_v1_pair_forest_marker_seed_v1')])
(E/'PCG_ASSOCIATIONS.json').write_text(json.dumps(results,indent=1)+'\n');print('Three source-fission bodies erase exactly to frozen callers')
