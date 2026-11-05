from pathlib import Path
import importlib.util,json,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('NHG_v4',E/'NHG_stage4_validate.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
results=[]
def mutate(name,file,change):
 p=E/file;raw=p.read_bytes()
 try:
  x=json.loads(raw);change(x);p.write_text(json.dumps(x))
  try:v.validate()
  except (AssertionError,KeyError,ValueError,StopIteration):results.append(dict(name=name,rejected=True));return
  raise RuntimeError('Mutation accepted: '+name)
 finally:p.write_bytes(raw)
mutate('retain eight old rows','NHG_CLOSED.json',lambda x:x['functions'].pop(0))
mutate('deny unpaired product oracle','NHG_CLOSED.json',lambda x:x['functions'][9].update(paired_product_laws=[]))
mutate('deny native field multiplication claim','NHG_CLOSED.json',lambda x:x['functions'][9].update(native_field_multiplication=True))
mutate('deny missing canonical alpha domain','NHG_CLOSED.json',lambda x:x['functions'][9].update(domain='arbitrary'))
mutate('deny unbounded range domain','NHG_CLOSED.json',lambda x:next(f for f in x['functions']if f['rows']==['TX1:262']).update(domain='unrestricted ranges'))
mutate('deny removed M31 arithmetic edge','NHG_CLOSED.json',lambda x:x['functions'][8].update(internal_edges=[]))
mutate('deny chosen-success premise','NHG_CLOSED.json',lambda x:x['functions'][8].update(inner_hypotheses_remaining=['assume success']))
mutate('deny fixture control success','NHG_K052/receipt.json',lambda x:x.update(exit_status=0))
mutate('deny false admission','NHG_K069-admission.json',lambda x:x['reservation'].update(allowed=False))
mutate('deny lock drift','NHG_K061-lock-check.json',lambda x:x.update(unchanged=False))
mutate('deny graph drift','NHG_K071-graph-check.json',lambda x:x.update(graph_matches_frozen=False))
mutate('deny sorry in raw traversal','NHG_audit/batch10/proof10.json',lambda x:x['results'][0].update(walked_axioms=['sorryAx']))
mutate('deny truncated root table','NHG_CONSTANT_PINS.json',lambda x:x.update(cells=167))
mutate('deny erased edge resolution','NHG_STAGE4_RESOLUTIONS.json',lambda x:x['TX1:135'].update(actual_edges=[]))
mutate('deny claims auto closure','NHG_CLOSED.json',lambda x:x['functions'].append(dict(rows=['TX1:129'],status='CLOSED')))
assert v.validate()['status']=='PASS'
(E/'NHG_STAGE4_MUTATIONS.json').write_text(json.dumps(results,indent=1)+'\n');print(len(results),'denial controls rejected; restored PASS')
