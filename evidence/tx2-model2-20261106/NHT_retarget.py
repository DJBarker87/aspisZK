from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
common=E.parent/'extract-stage-20261106/NHR_lean/NHR_tx2_common/Funs.lean'
s=common.read_text();body=s[s.index('def verifier.candidate.tx2_common\n'):s.index('\nend NHR_tx2_common')]
body=body.replace('def verifier.candidate.tx2_common\n','def tx2_common (ops : VTop_Stages.Ops)\n',1)
mapping={'NHR_call_0':'ops.op2','NHR_call_1':'ops.op5','NHR_call_2':'ops.op6','NHR_call_3':'ops.op17','NHR_call_4':'ops.op18','NHR_call_5':'ops.op19','NHR_call_6':'ops.op9','NHR_call_7':'ops.op10','NHR_call_8':'ops.op11','NHR_call_9':'ops.op13','compact.SPLIT':'10#usize'}
for c,o in {'OFF_INACTIVE':'23','OFF_ROUND0':'22','OFF_FOLDED_ROOT':'15','OFF_ROUND1':'14','OFF_FINAL':'21','OFF_OPENINGS':'20'}.items():mapping['compact.'+c]='ops.op'+o
mapping['core.option.Option.ok_or']='NHT_Constants.core.option.Option.ok_or'
# Keep emitted constants and unwrap transparent; do not introduce extra opaque cuts.
for key in list(mapping):
 if key.startswith('compact.'):
  mapping[key]='NHT_Constants.'+key
mapping.update({'verifier.Phase.':'AdapterRw.aspis_r1_cost_probe.verifier.Phase.','transport.Variant.S2':'AspisR1Stage2.transport.Variant.S2','verifier.Error.Parse':'AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse','verifier.Error.Checkpoint':'AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint'})
for a,b in mapping.items():body=body.replace(a,b)
header='import NHT_Constants\nset_option autoImplicit false\nnoncomputable section\nnamespace NHT_EmittedCommon\nopen Aeneas Aeneas.Std Result VTop_Stages\n'
(E/'NHT_EmittedCommon.lean').write_text(header+body+'\nend NHT_EmittedCommon\n')
auth=E.parent/'extract-stage-20261106/NHR_lean/NHR_tx2_authenticated/Funs.lean';s=auth.read_text();b=s[s.index('def verifier.candidate.tx2_authenticated\n'):s.index('\nend NHR_tx2_authenticated')]
b=b.replace('def verifier.candidate.tx2_authenticated\n','def tx2_authenticated (ops : VTop_Stages.Ops)\n',1)
am={'verifier.Phase.':'AdapterRw.aspis_r1_cost_probe.verifier.Phase.','NHR_call_0':'ops.op3','NHR_call_1':'NHT_EmittedCommon.tx2_common ops','NHR_call_2':'ops.op13'}
for a,v in am.items():b=b.replace(a,v)
(E/'NHT_EmittedAuth.lean').write_text(header.replace('import NHT_Constants','import NHT_EmittedCommon').replace('namespace NHT_EmittedCommon','namespace NHT_EmittedAuth')+b+'\nend NHT_EmittedAuth\n')
(E/'NHT_RETARGET.json').write_text(json.dumps({'inputs':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [common,auth]},'common_map':mapping,'auth_map':am,'nominal_port':'canonical VTop_Stages imported carrier owners; structural port, not raw nominal equality','nonopaque_changes':['relocate exact emitted constant definitions and option helper to NHT_Constants','preserve transparent standard-library unwrap; install exact helpers/constants in adopted Ops for source equality'],'caveat':'Port association to raw generated nominal types/native remains P6 obligation, never claimed by compilation'},indent=2)+'\n')
