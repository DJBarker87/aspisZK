"""Emit symbolic straight-line semantic caller proofs; branches get separate laws."""
from pathlib import Path
import sys,json
p=Path('tools/pv-b3p6-20261028/poseidon227_resume7.py');s=p.read_text().split("emit('PV_B3P_ExternalSuccess227'",1)[0]
ns={'__file__':str(p.absolute())};exec(s,ns)
wanted={'reference_terminal.reconstruct_10','reference_terminal.add_digest_binding','reference_terminal.add_schedule_lanes','reference_terminal.path_lanes_literal','reference_terminal.add_path_lanes','reference_terminal.add_value_lanes','reference_terminal.occupancy_lanes_literal','reference_terminal.add_occupancy_lanes'}
ns['mapping'].update({
 'reference_terminal.lift_m31':'lift_m31_total','reference_terminal.tweak227':'tweak_total',
 'reference_terminal.semantic_initial_and_absorption':'total_reference_terminal_semantic_initial_and_absorption',
 'reference_terminal.add_preweighted':'preweighted_total',
 'reference_copy_terminal.Selectors.row':'row_total',
 'reference_terminal.variant_expected_output':'variant_output_total'})
# Specialize the original straight-line emitter without changing any emitted body.
a=s.index('def emit(');emit_source=s[a:]
emit_source=emit_source.replace("  for name,head,body in extract(source):", "  for name,head,body in extract(source):\n   if name not in wanted:continue")
emit_source=emit_source.replace("   if name=='reference_poseidon.interpolate_column227':pass", "   if name=='reference_terminal.add_digest_binding':binders.append('(hstart : start.val≤8)')")
emit_source=emit_source.replace("    if name=='reference_poseidon.interpolated_internal_pair'", "    if target=='preweighted_total':return 'apply preweighted_total <;> scalar_tac'\n    if target=='row_total':return 'apply row_total; first | scalar_tac | (apply row_mul_bound; first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac)) | (apply row_address_bound <;> first | scalar_tac | (simp only [reference_terminal.VALUE_AUXILIARY_BLOCK]; scalar_tac))'\n    if target in ['read_total','interval_total']:return 'apply '+target+' <;> scalar_tac'\n    if target=='total_reference_terminal_add_digest_binding':return 'apply '+target+' <;> scalar_tac'\n    if target=='index':return 'apply index; first | scalar_tac | (apply wrap_add_bound; first | scalar_tac | (simp only [aspis_statement.poseidon2.RATE]; scalar_tac))'\n    if name=='reference_poseidon.interpolated_internal_pair'")
emit_source=emit_source.replace("    if expr.startswith('lift '):", "    if expr.split()[0]=='reference_terminal.INPUT_OCCUPANCY_ROW':proof+=['  apply input_row_bind'];continue\n    if expr.split()[0]=='reference_terminal.OUTPUT_OCCUPANCY_ROW':proof+=['  apply output_row_bind'];continue\n    if expr.startswith('lift '):")
ns['wanted']=wanted;exec(emit_source,ns)
ns['emit']('PV_B3P_SemanticCallersSuccess227',['PV_B3P_P227_08','PV_B3P_P227_10'],['PV_B3P_SemanticCellsSuccess227'])
if '--check'not in sys.argv:Path('evidence/pv-b3p6-20261028/resume7/semantic-generator.json').write_text(json.dumps(ns['records'],indent=2)+'\n')
print(len(ns['records']))
