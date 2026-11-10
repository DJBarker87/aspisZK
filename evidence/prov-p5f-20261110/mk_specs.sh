cd "$(dirname "$0")"
python3 -B - <<'PY'
import json,subprocess
Q='../prov-p1f-20261109/PCQG_%s_spec.json'
def C(e): return json.load(open(Q%e))['configuration']
INC='aspis_core::field::P,aspis_core::field::_::ZERO,aspis_core::field::_::ONE'
sop=[]
for e in ('E003','E010'): sop+=C(e)['start_from']
sop+=['crate::state_only_poseidon::interpolated_internal_pair','crate::state_only_poseidon::internal_linear_lazy']
sop=list(dict.fromkeys(sop))
subprocess.check_call(['python3','-B','PCWP_mkspec.py','PCWP_E002','PCWP_sop2','aspis-statement',C('E010')['features'],','.join(sop),INC])
sem=[]
for e in ('E007','E015'): sem+=C(e)['start_from']
sem=list(dict.fromkeys(sem))
print(len(sem),C('E007')['features']==C('E015')['features'])
json.dump(dict(sem=sem,feat7=C('E007')['features'],feat15=C('E015')['features']),open('gen/sem_roots.json','w'))
PY
rm -rf __pycache__
