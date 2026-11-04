"""Mutation tests of added gates; no proof reruns or inherited writes."""
from pathlib import Path
import importlib.util,json,copy,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('NGH_cert',E/'NGH_certify.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
N=m.N;original=N.J;passed=[]
def reject(label,mutation,filename='receipt.json'):
 def patched(p):
  x=copy.deepcopy(original(p))
  if p.parent.name=='NGH_K011'and p.name==filename:mutation(x)
  if filename!='receipt.json'and p.name=='NGH_K011'+filename:mutation(x)
  return x
 N.J=patched
 try:
  try:N.native(11,0)
  except (AssertionError,KeyError,TypeError):passed.append(label)
  else:raise RuntimeError('Mutation admitted: '+label)
 finally:N.J=original
reject('failed positive',lambda x:x.update(exit_status=1))
reject('swap',lambda x:x.update(swaps='1'))
reject('uncapped',lambda x:x.update(limits={}))
reject('offline removed',lambda x:x['env'].update(CARGO_NET_OFFLINE='false'))
reject('unoptimized',lambda x:x['env'].update(CARGO_PROFILE_DEV_OPT_LEVEL='0'))
reject('source tamper',lambda x:x['source_hashes'].update({next(iter(x['source_hashes'])):'0'*64}))
reject('admission exit78',lambda x:x.update(exit=78),'-admission.json')
reject('admission false',lambda x:x['reservation'].update(allowed=False),'-admission.json')
reject('dependency drift',lambda x:x.update(graph_matches_frozen=False),'-graph-check.json')
reject('features drift',lambda x:next(p for p in x['selected_closure']if p['name']=='aspis-core').update(features=[]),'-graph-check.json')
reject('lock changed',lambda x:x.update(unchanged=False),'-lock-check.json')
reject('lock hash drift',lambda x:x.update(after='0'*64),'-lock-check.json')
reject('source-check failure',lambda x:x.update(errors=['field.rs']),'-source-check.json')
for rid in ['TX1:036','TX1:044','TX1:040','TX1:041','TX1:043']:
 try:m.helper_gate(dict(row=rid,native_valid=True,actual_helper_contract=True,all_actual_callees_closed=True,raw_ax2_standard=True,reference_transcription=True))
 except AssertionError:passed.append('all-True helper flags rejected '+rid)
 else:raise RuntimeError('Fabricated helper contract admitted')
for label,mutation in [
 ('duplicate inversion cfg',lambda x:x['env'].update(RUSTFLAGS=x['env']['RUSTFLAGS']+' --cfg NGH_invert')),
 ('missing inversion cfg',lambda x:x['env'].update(RUSTFLAGS=x['env']['RUSTFLAGS'].replace('--cfg NGH_invert',''))),
 ('extra non-control cfg',lambda x:x['env'].update(RUSTFLAGS=x['env']['RUSTFLAGS']+' --cfg NGH_unexpected')),
 ('unmatched control environment',lambda x:x['env'].update(NGH_UNEXPECTED='1'))]:
 def patched_pair(p):
  x=copy.deepcopy(original(p))
  if p.parent.name=='NGH_K031'and p.name=='receipt.json':mutation(x)
  return x
 N.J=patched_pair
 try:
  try:N.pair(30,31)
  except (AssertionError,KeyError,TypeError):passed.append(label)
  else:raise RuntimeError('Mutation admitted: '+label)
 finally:N.J=original
assert len(passed)==22
(E/'NGH_TESTS.json').write_text(json.dumps(dict(status='PASS',mutations_rejected=passed,checks=22),indent=1)+'\n')
print('22 mutation checks passed')
