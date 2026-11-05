"""Check exact native-stage record projection; never execute predecessor validators."""
from pathlib import Path
import re,hashlib,json,copy
E=Path(__file__).resolve().parent
p=E.parent/'slice-d-pair4-20261107/NIG_stages.patch'
source='\n'.join(l[1:] for l in p.read_text().splitlines() if l.startswith('+') and not l.startswith('+++'))
expected={
 'new_cut':{'p':{'variant','semantic_alpha','z'}},
 'pair_cut':{'p':{'alpha','kappa'},'v':{'final_message'}},
 'finish_cut':{'p':{'claim','alpha','variant','semantic_alpha','z','kappa'},
               'v':{'round0','round1','final_message'},'a':{'weights','next','rhs'}}}
def body(text,name):
 m=re.search(r'\bfn '+re.escape(name)+r'\(',text);assert m,name
 start=text.index('{',m.end());depth=1;i=start+1
 while depth:
  if text[i]=='{':depth+=1
  elif text[i]=='}':depth-=1
  i+=1
 return text[start:i]
def validate(text):
 out={}
 for name,rows in expected.items():
  b=body(text,name);out[name]={}
  for arg,fields in rows.items():
   actual=set(re.findall(r'\b'+arg+r'\.([a-zA-Z_][a-zA-Z_0-9]*)',b))
   assert actual==fields,(name,arg,sorted(actual),sorted(fields))
   out[name][arg]=sorted(actual)
 return out
positive=validate(source);controls=[]
for name,rows in expected.items():
 for arg in rows:
  target=body(source,name);mutated=source.replace(target,target[:-1]+';let _='+arg+'.NIT_unreviewed_field;}')
  try:validate(mutated)
  except AssertionError:controls.append({'function':name,'argument':arg,'mutation':'extra field read','rejected':True})
  else:raise AssertionError('accepted mutated footprint')
# The native constructors seed unused p fields, but no cut reads or forwards
# those fields. This is a syntactic footprint projection, not a claim about
# arbitrary pointer payload identity or a new semantic trust row.
output={'source':str(p.relative_to(E.parent.parent)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
 'functions':positive,'rejected_controls':controls,'status':'source footprint projection only',
 'immutable_unread_prepared_fields':['roots','gamma','rho','queries','state'],
 'qualification':'Native stage reads/forwards only these fields; projection does not infer payload equality from pointer equality.'}
(E/'NIT_PROJECTION.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps({'positive':True,'controls_rejected':len(controls)}))
