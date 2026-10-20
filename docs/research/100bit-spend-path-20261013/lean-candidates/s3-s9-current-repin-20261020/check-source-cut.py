#!/usr/bin/env python3
from pathlib import Path
import argparse,hashlib,json,re
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,default=Path.cwd());ap.add_argument('--cut',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
def fn(src,name):
 i=src.index('fn '+name+'('); b=src.index('{',i); d=0
 for j in range(b,len(src)):
  if src[j]=='{':d+=1
  elif src[j]=='}':
   d-=1
   if d==0:return src[b+1:j]
 raise ValueError(name)
def arr(src,name):
 m=re.search(r'(?:pub\s+)?const\s+'+name+r'\s*:\s*\[[^]]+\]\s*=\s*\[([^]]*)\]',src,re.S); assert m,name
 return [int(x) for x in re.findall(r'\d+',m.group(1))]
prod=(a.repo/'crates/aspis-r1-cost-probe/src/weights.rs').read_text(); cut=a.cut.read_text(); norm=lambda s:re.sub(r'\s+','',s)
left=norm(fn(prod,'s2_grouped_inactive_pair')).replace('field(f,j)','coeff[j]'); right=norm(fn(cut,'s2_grouped_inactive_pair')); assert left==right,'function body mismatch after sole decoder substitution'
for n in ['S2_INACTIVE_GROUPS','S2_INACTIVE_MASKS']: assert arr(prod,n)==arr(cut,n),n
report={'status':'PASS','function':'s2_grouped_inactive_pair','production_weights_rs_sha256':hashlib.sha256((a.repo/'crates/aspis-r1-cost-probe/src/weights.rs').read_bytes()).hexdigest(),'candidate_lib_rs_sha256':hashlib.sha256(a.cut.read_bytes()).hexdigest(),'body_comparison':'equal after field(f,j) -> coeff[j], whitespace ignored','table_constants':['S2_INACTIVE_GROUPS','S2_INACTIVE_MASKS'],'boundaries':['field(f,j) result array','WideExact carrier/constants source cut','opaque add/mul child methods; correspondence theorem not yet checked']}
a.out.write_text(json.dumps(report,indent=2)+'\n'); print(json.dumps(report))
