from pathlib import Path
import json
D=Path('evidence/pv-b3q-20261029');x=json.loads((D/'std-source-association.json').read_text());mapping={
'core::result::branch':['PV_B3Q_Std.partial_catalogue_link','PV_B3Q_Std.binding_result_branch'],
'core::result::from_residual':['PV_B3Q_ResultResidual.residual_link'],
'core::result::from_output':['PV_B3Q_StdValues.values_link'],
'core::convert::from':['PV_B3Q_StdValues.values_link'],
'core::option::unwrap_or':['PV_B3Q_Std.binding_u32_unwrap_or'],
'core::option::is_some':['PV_B3Q_Std.binding_u32_is_some'],
'core::convert::num::from':['PV_B3Q_Std.partial_catalogue_link'],
'core::num::checked_add':['PV_B3Q_CheckedAdd.checked_add_link'],
'core::num::wrapping_add':['PV_B3Q_Wrapping.wrappers_link'],
'core::num::wrapping_sub':['PV_B3Q_Wrapping.wrappers_link'],
'core::num::count_ones':['PV_B3Q_BitCounts.wrappers_link'],
'core::num::trailing_zeros':['PV_B3Q_BitCounts.wrappers_link'],
'core::cmp::PartialEq::ne':['PV_B3Q_OptionEquality.ne_binding'],
'core::cmp::impls::eq':['PV_B3Q_CompareActual.primitive_comparison_links'],
'core::cmp::impls::ne':['PV_B3Q_CompareActual.primitive_comparison_links'],
'core::option::eq':['PV_B3Q_OptionEquality.option_links'],
'core::clone::impls::clone':['PV_B3Q_CloneActual.primitive_clone_links'],
'core::clone::Clone::clone_from':['PV_B3Q_CloneActual.primitive_clone_links'],
'core::slice::cmp::equal_same_length':['PV_B3Q_SliceEqual.source_link','PV_B3Q_SliceEqualityValue.slice_value_link','PV_B3Q_SliceActual.actual_slice_link','PV_B3Q_M31SliceActual.actual_slice_link'],
'core::slice::len':['PV_B3Q_ArrayView.view_length']}
for row in x['conservative_source_union']:
 row['candidate_source_binding_theorems']=mapping.get(row['name'],[])
 if row['name'].startswith('core::array::equality::'):
  row['candidate_source_binding_theorems']=['PV_B3Q_ByteArrayEq.specialized_link (actual [u8;32] specialization only)','PV_B3Q_SliceEqualityValue.slice_value_link (M31/U32 scalar comparison value port)']
 row['status']='local documented-carrier instance only; exact signature/carrier and source-step dossier required'if row['candidate_source_binding_theorems']else'OPEN: no full concrete source binding supplied'
 if row['name'].startswith('core::fmt::')or 'encode_utf8'in row['name']or row['name'].startswith('core::panicking::'):
  row['status']='OPEN: formatting/panic source reachability or faithful model required; see FORMATTER-FINDING.md'
out=dict(existing_link='PV_B3P_Groups14227.PV_B3P_Link_std_dependency_closure14',status='PARTIAL; complete concrete deployed catalogue is NOT discharged',conservative_capture_entries=len(x['conservative_source_union']),entries=x['conservative_source_union'],additional_pre_inline_source_dossier='index-source-association.json',actual_signature_instances=['PV_B3Q_CloneActual.primitive_clone_links','PV_B3Q_CompareActual.primitive_comparison_links'],refuted_candidate='unconditional numeric formatting with rejecting writer versus always-Ok DisplayUsize; actual-function proof quarantined by pinned core.fmt.Formatter axiom; only the literal-port refutation is credited',omission_certificate=False,source_cone_completeness=False,boundary='V370 / pending D381,D386 retained; no new T item',body_count_policy='Inherited 79 conservative application candidates and 41 BOUND statuses are unchanged. Local standard ports are not added to that application-body count.')
(D/'catalogue-status.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'])
