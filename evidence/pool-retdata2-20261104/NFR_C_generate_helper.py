"""Body-preserving helper extraction adaptation; external templates remain text."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;D=E/'NFR_C_E001_outputs'
t=(D/'NFR_C_helper_extracted__NFR_CHelperExtracted__Types.lean.txt').read_text()
f=(D/'NFR_C_helper_extracted__NFR_CHelperExtracted__Funs.lean.txt').read_text()
start=t.index('@[discriminant u32');end=t.index('/-- [solana_program_error::ProgramError]',start)
typeblock=t[start:end]
typeblock=re.sub(r',\s*rust_type "aspis_pool::error::PoolV1ProgramError"','',typeblock)
body=f[f.index('/-- [aspis_pool::error::'):f.rindex('end NFR_CHelperExtracted')]
body=re.sub(r'/--[\s\S]*?-/', '',body);body=re.sub(r'@\[[\s\S]*?\]','',body)
name='solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError'
body=body.replace(name+'.from','convertPoolError').replace(name,'poolErrorFrom')
body=body.replace('aspis_statement.','AspisR1TerminalDecoder.').replace('solana_program_error.ProgramError','AdapterRw.solana_program_error.ProgramError')
body=body.replace('def terminal_result_bytes_box_v1\n','def terminal_result_bytes_box_v1\n  (encoder : NEU_EmitModel.Output → Result (core.result.Result (Array U8 792#usize) NEU_EmitModel.Error))\n')
body=body.replace('AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1\n      result','encoder result')
body=body.replace('def terminal_ref\n','def terminal_ref\n  (encoder : NEU_EmitModel.Output → Result (core.result.Result (Array U8 792#usize) NEU_EmitModel.Error))\n').replace('  terminal_result_bytes_box_v1 result','  terminal_result_bytes_box_v1 encoder result')
source='''import NFR_CSettlement
set_option autoImplicit false
noncomputable section
namespace NFR_CHelper
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1TerminalDecoder
'''+typeblock+'\ndef terminal_result_bytes_box_v1.closure := Unit\n'+body+'''

theorem accepted (encoder : NEU_EmitModel.Output → Result (core.result.Result (Array U8 792#usize) NEU_EmitModel.Error))
    (r : NEU_EmitModel.Output) (bytes : Array U8 792#usize)
    (encoded : encoder r = ok (.Ok bytes)) :
    terminal_ref encoder r = ok (.Ok bytes) := by
  unfold terminal_ref terminal_result_bytes_box_v1
  rw [encoded]
  rfl

theorem rejected (encoder : NEU_EmitModel.Output → Result (core.result.Result (Array U8 792#usize) NEU_EmitModel.Error))
    (r : NEU_EmitModel.Output) (e : NEU_EmitModel.Error)
    (encoded : encoder r = ok (.Err e)) :
    terminal_ref encoder r = ok (.Err NFR_CSettlement.invalidReturn) := by
  unfold terminal_ref terminal_result_bytes_box_v1
  rw [encoded]
  rfl

#print axioms accepted
#print axioms rejected
end NFR_CHelper
'''
(E/'NFR_CHelper.lean').write_text(source)
manifest=dict(input_types_sha256=hashlib.sha256(t.encode()).hexdigest(),input_body_sha256=hashlib.sha256(f.encode()).hexdigest(),output_sha256=hashlib.sha256(source.encode()).hexdigest(),adaptations=['namespace NFR_CHelperExtracted -> NFR_CHelper','reuse canonical AspisR1TerminalDecoder Result/Error and AdapterRw ProgramError carriers','retain emitted PoolV1ProgramError enum/discriminants and error conversion unchanged','replace sole external encoder by explicit dictionary parameter at same call site','reuse already defined core.Result.map_err/try/from_residual generics; no external template imported','strip rust source comments/reflection attributes; no proof-depth/heartbeat settings added'])
(E/'NFR_C_HELPER_ADAPTATION.json').write_text(json.dumps(manifest,indent=1)+'\n')
