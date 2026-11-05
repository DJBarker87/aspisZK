from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent
p=E/'NIV_extracted/entry/raw/NIV_entry/Funs.lean';raw=p.read_text()
b=raw[raw.index('/-- [aspis_r1_cost_probe_program::r1_pool_adapter::process]'):raw.index('end NIV_entry')]
b=b.replace('def r1_pool_adapter.process\n','def process {Account : Type} (ops : Hiq_DispatchSource.Ops Account)\n').replace('def process_r1_cost_probe_instruction\n','def entry {Account : Type} (ops : Hiq_DispatchSource.Ops Account)\n')
for old,new in [('solana_pubkey.Pubkey','Hiq_DispatchSource.Key'),('solana_account_info.AccountInfo','Account'),('solana_program_error.ProgramError','Hiq_DispatchSource.PE'),('core.slice.Slice.first','Hiq_DispatchSource.firstByte'),('core.option.OptionShared0T.copied core.marker.CopyU8','Hiq_DispatchSource.copied'),('Slice.Insts.CoreCmpPartialEqArray.eq core.cmp.PartialEqU8','Hiq_DispatchSource.eqU8'),('r1_pool_adapter.owned.stage1','ops.first'),('r1_pool_adapter.owned.stage2','ops.second'),('r1_pool_adapter.lifecycle_init','ops.init'),('r1_pool_adapter.lifecycle_write','ops.write'),('r1_pool_adapter.lifecycle_finalize','ops.finalize'),('pool_route.admitted','Hiq_DispatchSource.pool_route.admitted'),('r1_pool_adapter.process program_id','process ops program_id')]: b=b.replace(old,new)
# Use the existing canonical PE constructor directly, preserving its sole owner.
b=b.replace('Hiq_DispatchSource.PE.InvalidInstructionData','AdapterRw.solana_program_error.ProgramError.InvalidInstructionData')
s='''import Hiq_DispatchRelease
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIV_ExtractedForward
open Aeneas Aeneas.Std Result
/- Actual extraction body, with opaque boundaries parameterized and canonical
    types/primitives reused. See NIV_PARAMETERIZATION.json; no template axiom. -/
'''+b+'''
theorem process_source {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8) :
    process ops p a d = Hiq_DispatchSource.r1_pool_adapter.process ops p a d := rfl

theorem entry_source {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8) :
    entry ops p a d = Hiq_DispatchSource.process_r1_cost_probe_instruction ops p a d := rfl

/-- Complete result, including foreign error payloads, divergence and failure;
    all three descriptors are unchanged at the selected child boundary. -/
theorem forwarding {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8) :
    entry ops p a d = match Hiq_ReleaseRoute.route d with
      | .first => ops.first p a d
      | .second => ops.second p a d
      | .reject => ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidInstructionData) := by
  rw [entry_source]
  exact Hiq_DispatchRelease.source ops p a d

#print axioms process_source
#print axioms entry_source
#print axioms forwarding
end AspisR1.NIV_ExtractedForward
end
'''
(E/'NIV_ExtractedForward.lean').write_text(s)
(E/'NIV_PARAMETERIZATION.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(s.encode()).hexdigest(),transformations=['drop unused generic trait implementation','parameterize six opaque functions with existing Ops and admitted route','canonical AdapterRw Pubkey/ProgramError owner','specialize emitted U8 slice primitives to existing source definitions'],axiom_templates_compiled=False,native_sdk_effects_claim=False),indent=2)+'\n')
