"""Record bundle definitions and classify inherited hypotheses; no row credit."""
from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
p=E/'LIB_STATUS.json';rows=json.loads(p.read_text());s=(E/'LIB_VLib.lean').read_text();mp=dict(re.findall(r'^ (\w+) := (\S+)',s,re.M))
for row in rows:
 if row.get('struct')=='VLib' and row['field'] in mp:
  f=row['field'];row.update(status='DONE',module='LIB_VLib',theorem='LIB_VLib.'+f+'_exact',defining_term='LIB_VLib.library.'+f,supplier_definition=mp[f],reason='Actual canonical VL-star; same merged supplier graph/domain, definitional projection L182')
  if 'theorem '+f+'_returns ' in s:row['returns']='LIB_VLib.'+f+'_returns';row['evaluator']='LIB_VLib.'+f+'Value'
 if row.get('struct')=='PreparedNew':row.update(status='DONE',module='LIB_Prepared',theorem='LIB_Prepared.exact_graph',defining_term='LIB_Prepared.child',reason='Actual canonical P-star; carrier identities rfl L183; original caller clauses retained')
 if row.get('struct')=='S1Lib':
  row.update(status='DONE',module='LIB_S1',defining_term='LIB_S1.library.'+row['field'],reason='Actual canonical C-star at SAME VL-star L184; source laws reused from LIBC_S1Sources/LIBC_S1')
p.write_text(json.dumps(rows,indent=2)+'\n')
p=E/'LIB_CLOSED.json';x=json.loads(p.read_text())
x['bundle_continuation']={
 'definitions':{'VL':'LIB_VLib.library','P':'LIB_Prepared.child','C':'LIB_S1.library','TX1':'LIB_Instances.tx1'},
 'carrier_equalities':'discharged by rfl at actual VL; no operational parameter',
 'per_field_graphs':f'all{len(mp)} projections equal merged supplier definitions at same arguments;20 Returns evaluators',
 'principal_rows':'not claimed; type checks identify exact TAS field types only',
 'retained':'All original supplier caller clauses, Env/runtime realization, std/allocator/native-tool trust, source-to-ELF and extraction provenance remain; no new assumption or trust item',
 'new_trust':[],
 'hypotheses':{
  'LIB_VLib':'Only own-input clauses inherited definitionally from each merged supplier; Returns are unconditional',
  'LIB_Prepared':'No top model or operation parameter; generic input/output/runtime arguments only. child.dom remains LIBC_PreparedDomain.Domain at same input',
  'LIB_S1.validated_public':'SAME statement validator true; antecedent proved by principal on its validated branch',
  'LIB_S1.allocation':'Exact original native bytes; before-first-Box probe; no eventual-success predicate',
  'LIB_Instances.tas_checks':'Arbitrary L/V0/Impl parameters only to state type equality; no claim those rows are instantiated'
 }}
p.write_text(json.dumps(x,indent=2)+'\n')
p=E/'LIB_CALLER_CLAUSES.json';x=json.loads(p.read_text());x['bundle_continuation']={
 'changes':[],
 'VLib':'Every dom and law equals its original lane-A/C supplier by LIB_VLib.<field>_exact',
 'Prepared':'LIB_Prepared.caller_clauses preserves SAME input provenance; LIBC_PreparedR4.expanded remains available to principal',
 'S1':'LIB_S1.validated_public and allocation specialize SAME statement/bytes; no new caller premise',
 'R4':'LIB_VLib.checkValuesDom_exact fixes LIBC_CheckValuesDomain.checkValuesDom; LIBC_CanonicalScan.r4_value retained',
 'F6':'LIB_VLib.checkpoint_exact fixes LIBC_Checkpoint.child; current-pair DriverEstablishedDomain retained'}
p.write_text(json.dumps(x,indent=2)+'\n')
