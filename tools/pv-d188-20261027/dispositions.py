from pathlib import Path
import json
out=Path('evidence/pv-d188-20261027');decls=json.loads((out/'mutable-declarations.json').read_text());r=[]
byfile={
 'ProverRwSampler/Funs.lean':('28104/native-001','Indexed division/decoding carries each updated array into the next iteration.'),
 'PV_CB_Op72Funs.lean':('28102/native-001','Every slice back function consumes the modified subslice and its enclosing slice is returned/carried.'),
 'PV_CB_Op118Funs.lean':('28107/native-002','Array.update outputs feed the next loop state or returned absorption array.'),
 'PV_CBL_ArrayKernel.lean':('28108/native-002','Array.update result is the carried output; Copy/fixed-size reference scope only.'),
 'PV_CBL_ShaPadFixed.lean':('28108/native-002','Updated buffers are carried/returned, including the suffix stores.'),
 'PV_CBL_FallbackBlock.lean':('28109/native-002','All eight state updates are returned; fallback-reference scope only.'),
 'PV_CB_Op223TupleProducerFuns.lean':('28115/native-004','Each modified limb array is carried to the next range iteration. Concrete contains binding implements the real comparison.'),
 'PV_CB_Op223ForestProducerFuns.lean':('28115/native-004','Each modified limb array is carried to the next range iteration.'),
 'PV_B1_254_Funs.lean':('28112/native-002','Old element is discarded, restoration callback is retained and applied to p on both branches.'),
 'ProverRwRngMaterialBodyEmission.lean':('28111/native-002','Four modified subranges restore the successive whole array; frozen version constant supplied explicitly.'),
 'ProverRwRngNativeBodyEmission.lean':('same encode body as 28111/native-002','Same encode function shape; no mutable-back result is discarded. Whole native entropy effects remain unproved.'),
 'PV_R2_DF_249_04_Funs.lean':('28106/native-001','Every quotient/digit Array.update output is carried. This is the indexed reference, not the raw iterator emission.'),
 'PV_OrdinarySource.lean':('28120/native-001','Each quotient/digit Array.update output is carried; native original association remains a separate obligation.'),
 'PV_CB_OwnedEncoder.lean':('28123/native-006','Cell update is the returned array; native owned-helper comparison with a real M31 CodeField instance. No new original encoder association.'),
 'PV_CB_OwnedMask.lean':('28123/native-006','Cell update is the returned array; no borrowed restoration callback exists. Reference-helper scope only.'),
 'PV_R2_DF_226_04_Funs.lean':('28116/native-005','Updated byte buffer is the carried loop state. Native prototype comparison only; original transport association stays suspended.'),
 'PV_R2_DF_252_05_Funs.lean':('28117/native-005','Each explicitly indexed point/factor array update is consumed. Native prototype comparison of every factor on a base-field fixture; original weights association stays suspended.')}
fullchecked=['aspis_prover.state_only_hiding.active_rows_loop.body','aspis_prover.state_only_entropy.source_active_flags_loop.body','aspis_prover.state_only_hiding.mask_dependent_step','host_tree.count_level_loop.body','host_transcript.scan_query_words','host_semantic.boolean_point_loop.body','host_sumcheck.interpolation_accumulate_loop.body','host_sumcheck.interpolation_basis_cell','host_sumcheck.interpolation_basis','host_sumcheck.evaluate_assignment_loop.body','aspis_prover.state_only_hiding.balance_m31_copy_inactive','aspis_prover.state_only_hiding.balance_qm31_copy_inactive']
for d in decls:
 e=dict(d);key=next((k for k in byfile if d['file'].endswith(k)),None)
 if key:
  e.update(classification='CREDIT STANDS',evidence=byfile[key][0],static_argument=byfile[key][1],scope='Only the tested/helper model or existing source law; not a whole native row closure.')
 elif d['file'].endswith('ProverRwFullFuns.lean') and d['declaration'] in fullchecked:
  e.update(classification='CREDIT STANDS',evidence='28124/native-007; isolated math helpers 28126/28128–28131/28134–28136/native-008 as applicable',static_argument='Updated array/slice is carried/returned; concrete write-changing native comparison agrees.',scope='This closed helper only; full native composition remains suspended.')
 else:
  e.update(classification='SUSPENDED',evidence='MUTABLE-DECLARATIONS.md; inventory.json',static_argument='No discarded restoration is inferred merely from lexical matches; per-function closed native comparison/source association is not recorded here.',scope='Unchecked historical/reference/dictionary-dependent candidate; existing mathematical theorem is not invalidated.')
 r.append(e)
(out/'function-dispositions.json').write_text(json.dumps(r,indent=2)+'\n')
print('CREDIT STANDS',sum(d['classification']=='CREDIT STANDS' for d in r),'SUSPENDED',sum(d['classification']=='SUSPENDED' for d in r))
