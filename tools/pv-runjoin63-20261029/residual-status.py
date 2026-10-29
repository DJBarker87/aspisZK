from pathlib import Path
import json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin63-20261029'
s=json.loads((R/'evidence/pv-runjoin62-20261029/residual-ops.json').read_text())
s['entry_revision']='65a5f8ecf3ea29c7c919eb5298edab247729f261'
s['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
s['dictionary_after']='PV_RunJoin_NativeResidual63.opsNative base heap box ops runtime world'
for row in s['residual_fields']:
 if row['number']==32:
  row.update(status='CONFIRM qualified world-indexed structural packet; selected, not world-free',installation_theorem='PV_RunJoin_Packets63.reserve; PV_RunJoin_AllocatorWorld63.complete/execution/sequential',dictionary_after='Explicit allocator runtime and world; original complete Result and error encoding retained; dynamic whole-capture world interpretation still open')
 elif row['number']==132:
  row.update(status='CONFIRM selected structural source/value packet',installation_theorem='PV_RunJoin_Packets63.mask_source/mask_reference/mask_value/mask_count/mask_nonvacuity',dictionary_after='Installed; all3803 ordered cells; exact capacity/source predicates, original carrier and261 frames')
 elif row['number'] in [227,257]:
  row['dictionary_after']='Uninstalled residual field; preserved exactly by PV_RunJoin_NativeFrames63'
 else:
  row['dictionary_after']+='; retained at run63 by PV_RunJoin_NativeBinding63.native'
for row in s['additional_publication_residuals']:
 if row['field']=='op4':row.update(status='CONFIRM qualified inventoried Vec<u32>/Global destructor only',installation='PV_FXM_DropSelected.selected composed in NativeResidual63.residual; other types retain old op4')
s['uninstalled_reachable_fields']=[227,257]
s['open_prefix_obligations']=['V244/op227: native terminal source/value interpretation and successful reached call', 'V263/op257: native world worker interpreter, scheduling/effects and successful reached call']
s['minimal_success_definitions']={'V244':'PV_RunJoin_ResidualSuccess63.Op227Success','V263':'PV_RunJoin_ResidualSuccess63.Op257Success'}
s['minimal_success_sufficiency']='REFUTED for arbitrary residual ops by PV_RunJoin_ResidualObstruction63.insufficient. Both arbitrary-input existentials can hold while no capture exists. Binding the native worker interpreter remains necessary and is not hidden in a success predicate.'
s['whole_capture_world_threading']='OPEN. P/runs/Links are indexed by runtime and world. The per-request sequential post-world continuation is checked, but the unchanged Result-only NativeControl.run has not been joined to a dynamically evolving effect-world interpreter.'
s['runtime_adequacy']='rdea-1 retained for public-size allocation outcomes and failure independence. ReserveAdequacy63 exposes exact arithmetic guards and the actual request outcome, not an unconditional allocation success law.'
s['rows_removed']=[]
(E/'residual-ops.json').write_text(json.dumps(s,indent=2)+'\n')
