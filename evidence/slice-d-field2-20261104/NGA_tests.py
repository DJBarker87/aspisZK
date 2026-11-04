"""Mutation gates for false source-cut and open-child promotions; no prover launch."""
from pathlib import Path
import importlib.util,copy,json,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('NGA_certify',E/'NGA_certify.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
rows=[]
for rid,_,_ in m.SPECS:
 c=dict(row=rid,native_valid=True,same_input_domain_proved=True,emitted_association_valid=True,all_actual_callees_closed=True,combined_scan_valid=True,raw_ax2_standard=True,same_full_value_and_frame=True,trust_changes=[])
 variants=[('all_true_flags_cannot_launder_actual_gap',c)]
 for key in ['native_valid','same_input_domain_proved','emitted_association_valid','all_actual_callees_closed','combined_scan_valid','raw_ax2_standard','same_full_value_and_frame']:
  v=copy.deepcopy(c);v[key]=False;variants.append((key,v))
 v=copy.deepcopy(c);v['trust_changes']=['new hypothetical runtime assumption'];variants.append(('new_trust',v))
 for name,v in variants:
  try:m.checked_claim(v)
  except AssertionError as e:rows.append(dict(row=rid,mutation=name,rejected=True,reason=str(e)))
  else:raise AssertionError(('Unsound claim admitted',rid,name))
(E/'NGA_TESTS.json').write_text(json.dumps(dict(status='PASS',mutations=len(rows),results=rows),indent=2)+'\n')
print(json.dumps(dict(status='PASS',mutations=len(rows))))
