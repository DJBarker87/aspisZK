"""Emit the four source-small Box wrapper specifications, with exact call tuples."""
from pathlib import Path
E=Path(__file__).resolve().parent
rows=[(311,'B32 × B32 × AccountInfo','Checkpoint','decode_retained_pair_forest_checkpoint_account_v1','a'),(312,'B32 × B32 × UInt8 × AccountInfo','LaneState','decode_lane_account_from_program_invariant_v1 (writable=true)','(a,true)'),(313,'B32 × AccountInfo','Master','decode_master_account (writable=false)','(a,false)'),(314,'Bytes','Request','decode_pool_v1_pair_forest_terminal_request_v1; map all errors to InvalidInstructionData','a')]
for n,args,ret,callee,call in rows:
 childargs='('+args+') × Bool' if n in [312,313] else args
 s=f'''import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_{n}
open RSL PCM PCM.Computation
abbrev Args := {args}
/-- Frozen real callee: {callee}. Its graph and domain must be installed
at the SAME arguments; this module is supporting work until that installation. -/
abbrev Decoder := Child ({childargs}) {ret}
def Ref (decoder : Decoder) (a : Args) : Computation {ret} := do
  let value ← decoder.call {call}
  alloc
  Computation.pure value
def RowSpec (decoder : Decoder)
    (impl : Args → State → Env → Observation {ret}) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref decoder) impl
end PCM_POOL_{n}
'''
 (E/f'PCM_Spec_POOL_{n}.lean').write_text(s)
print('PCM Box specs emitted: 311,312,313,314')
