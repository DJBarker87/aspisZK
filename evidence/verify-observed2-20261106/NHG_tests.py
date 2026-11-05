from pathlib import Path
import json,importlib.util,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('NHG_admission',E/'NHG_validate.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
results=[]
def mutation(name,path,transform):
 p=E/path;old=p.read_bytes()
 try:
  p.write_bytes(transform(old))
  try:v.validate()
  except (AssertionError,KeyError,ValueError):results.append(dict(name=name,rejected=True))
  else:raise RuntimeError('mutation accepted: '+name)
 finally:p.write_bytes(old)
def jset(k,val):
 def f(raw):
  x=json.loads(raw);x[k]=val;return json.dumps(x).encode()
 return f
mutation('strict control must fail','NHG_K020/receipt.json',jset('exit_status',0))
mutation('frozen graph required','NHG_K003-graph-check.json',jset('graph_matches_frozen',False))
mutation('lock cannot drift','NHG_K005-lock-check.json',jset('unchanged',False))
def deny(raw):
 x=json.loads(raw);x['reservation']['allowed']=False;return json.dumps(x).encode()
mutation('admission requires allowed true','NHG_K007-admission.json',deny)
mutation('compiled source hash required','NHG_FieldSpec.lean',lambda b:b+b'\n-- altered input\n')
def bad_axiom(raw):
 x=json.loads(raw);x['results'][0]['walked_axioms'].append('NHG_bad_axiom');return json.dumps(x).encode()
mutation('raw standard-only axioms required','NHG_audit/batch1/proof1.json',bad_axiom)
def bad_edge(raw):
 x=json.loads(raw);next(f for f in x['functions']if f['rows']==['TX1:255'])['internal_edges']=[];return json.dumps(x).encode()
mutation('semantic callee edges required','NHG_CLOSED.json',bad_edge)
def no_qualifier(raw):
 x=json.loads(raw);next(f for f in x['functions']if f['rows']==['TX1:252'])['capacity_qualification']='capacity proved natively for all Vecs';return json.dumps(x).encode()
mutation('capacity and allocator qualification retained','NHG_CLOSED.json',no_qualifier)
def empty_domain(raw):
 x=json.loads(raw);next(f for f in x['functions']if f['rows']==['TX1:252'])['domain']='all Vecs';return json.dumps(x).encode()
mutation('nonempty initialized prefix domain explicit','NHG_CLOSED.json',empty_domain)
mutation('headline joint import required','NHG_COMBINED_IMPORT.lean',lambda b:b.replace(b'import NGK_COMBINED_IMPORT\n',b''))
def root_promotion(raw):
 x=json.loads(raw);x['functions'][0]['rows'].append('TX1:137');return json.dumps(x).encode()
mutation('verify_observed cannot be promoted','NHG_CLOSED.json',root_promotion)
def drop_inherited(raw):
 x=json.loads(raw);x['files'].pop(next(iter(x['files'])));return json.dumps(x).encode()
mutation('all inherited evidence remains required','NHG_NGX_DEEP_PINS.json',drop_inherited)
def change_plan(raw):
 x=json.loads(raw);x[0]['unchanged_positive_configuration']=False;return json.dumps(x).encode()
mutation('positive source equivalence required','NHG_STRICT_CONTROL_PLAN.json',change_plan)
(E/'NHG_MUTATION_RESULTS.json').write_text(json.dumps(results,indent=1)+'\n');assert len(results)==13;print(json.dumps(dict(status='PASS',mutations_rejected=len(results))))
