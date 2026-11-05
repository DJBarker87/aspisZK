"""Admission-denial controls; preserve every immutable old check."""
from pathlib import Path
import importlib.util,json,copy,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('NHG_v3',E/'NHG_stage3_validate.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
results=[]
def mutate(name,file,change):
 p=E/file;raw=p.read_bytes()
 try:
  x=json.loads(raw);change(x);p.write_text(json.dumps(x))
  try:v.validate()
  except (AssertionError,KeyError,ValueError,StopIteration):results.append(dict(name=name,rejected=True));return
  raise RuntimeError('Mutation accepted: '+name)
 finally:p.write_bytes(raw)
mutate('old certificate cannot disappear','NHG_CLOSED.json',lambda x:x['functions'].pop(0))
mutate('frontier child edge required','NHG_CLOSED.json',lambda x:x['functions'][4].update(internal_edges=[]))
mutate('producer chosen success premise forbidden','NHG_CLOSED.json',lambda x:x['functions'][5].update(inner_hypotheses_remaining=['serializer success']))
mutate('source transport cannot be removed','NHG_CLOSED.json',lambda x:x['functions'][5].update(source_transport='empirical only'))
mutate('retained capacity interpretation mandatory','NHG_CLOSED.json',lambda x:x['functions'][5].update(capacity_qualification='caller must have cap1884'))
mutate('corrected carrier control required','NHG_CLOSED.json',lambda x:x['functions'][6].update(matched_control=['NHG_K030']))
mutate('begin exact callee edges required','NHG_CLOSED.json',lambda x:x['functions'][7].update(internal_edges=['TX1:143']))
mutate('deny negative success','NHG_K048/receipt.json',lambda x:x.update(exit_status=0))
mutate('deny refused admission','NHG_K045-admission.json',lambda x:x['reservation'].update(allowed=False))
mutate('deny frozen graph drift','NHG_K047-graph-check.json',lambda x:x.update(graph_matches_frozen=False))
mutate('deny changed lock','NHG_K042-lock-check.json',lambda x:x.update(unchanged=False))
mutate('deny nonstandard raw axiom','NHG_audit/batch7/proof7.json',lambda x:x['results'][0].update(walked_axioms=['sorryAx']))
mutate('deny opaque field method resolution','NHG_RESOLUTIONS.json',lambda x:x.update(index_receiver='M31'))
mutate('deny frozen receiver source pin drift','NHG_RESOLUTIONS.json',lambda x:x['frozen_source_pins'].update({'crates/aspis-core/src/field.rs':'0'*64}))
mutate('deny trust removal claim','NHG_CLOSED.json',lambda x:x['functions'][5].update(trust='trust removed'))
mutate('deny wrong function inventory binding','NHG_CLOSED.json',lambda x:x['functions'][5].update(function='wrong::function'))
assert v.validate()['status']=='PASS' 
(E/'NHG_STAGE3_MUTATIONS.json').write_text(json.dumps(results,indent=1)+'\n')
print(len(results),'denial mutations rejected; restored candidate PASS')
