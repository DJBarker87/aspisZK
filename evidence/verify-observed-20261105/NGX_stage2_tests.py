from pathlib import Path
import json,importlib.util,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('NGX_admission',E/'NGX_stage2_validate.py');v=importlib.util.module_from_spec(sp);sp.loader.exec_module(v)
results=[]
def mutation(name,path,change):
 p=E/path;before=p.read_bytes()
 try:
  p.write_bytes(change(before))
  try:v.validate()
  except (AssertionError,KeyError,ValueError):results.append(dict(name=name,rejected=True))
  else:raise RuntimeError('Mutation accepted: '+name)
 finally:p.write_bytes(before)
def jset(key,value):
 def apply(raw):
  x=json.loads(raw);x[key]=value;return json.dumps(x).encode()
 return apply
mutation('control cannot pass','NGX_K009/receipt.json',jset('exit_status',0))
mutation('graph cannot drift','NGX_K011-graph-check.json',jset('graph_matches_frozen',False))
mutation('lock cannot change','NGX_K013-lock-check.json',jset('unchanged',False))
mutation('headline import required','NGX_COMBINED_IMPORT.lean',lambda b:b.replace(b'import NGK_COMBINED_IMPORT\n',b''))
mutation('fresh source hash required','NGX_SampleTrace.lean',lambda b:b+b'\n-- altered input\n')
def badroot(raw):
 x=json.loads(raw);x['results'][0]['walked_axioms'].append('NGX_bad_axiom');return json.dumps(x).encode()
mutation('nonstandard axiom rejected','NGX_audit/batch1/proof1.json',badroot)
def badcallee(raw):
 x=json.loads(raw);next(f for f in x['functions'] if f['rows']==['TX1:151'])['internal_edges']=[];return json.dumps(x).encode()
mutation('callee edge cannot vanish','NGX_CLOSED.json',badcallee)
def badtrace(raw):
 x=json.loads(raw);next(f for f in x['functions'] if f['rows']==['TX1:144'])['ordered_effect_roots']=[];return json.dumps(x).encode()
mutation('ordered-effects law required','NGX_CLOSED.json',badtrace)
def badadmission(raw):
 x=json.loads(raw);x['reservation']['allowed']=False;return json.dumps(x).encode()
mutation('allowed false cannot launch','NGX_K015-admission.json',badadmission)
assert v.validate()['status']=='PASS'
(E/'NGX_TESTS.json').write_text(json.dumps(dict(status='PASS',mutations=results),indent=1));print(json.dumps(dict(status='PASS',rejected=len(results))))
