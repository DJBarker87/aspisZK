"""Exact monad generalization of normalized E003 bodies; body identity is checked in Lean."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
ops_source=(E.parents[1]/'docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean').read_text()
fields={int(m.group(1)):m.group(0) for m in re.finditer(r'^  op(\d+) : .*?(?=^  op\d+ : |^\n\n)',ops_source,re.M|re.S)}
header='''import NMS_Emitted241
set_option autoImplicit false
noncomputable section
namespace NMS_Effect242
open Aeneas Aeneas.Std Result AdapterRw
variable {M : Type → Type} [Monad M] [MonadLift Result M]
local instance : MonadLift Result Result where
 monadLift := id
'''
selected=[9,17,20,23,37,45,51,52]
s=header+'structure Effects (M : Type → Type) where\n'+''.join(fields[n].replace('Result','M',1) for n in [])
# Replace only the final outer Result in each function signature; inner Rust
# Result is qualified and deliberately retained in full.
for n in selected:
 field=fields[n]
 field=re.sub(r'(?<!\.)\bResult\b', 'M',field)
 s+=field
s+='''  data : r1_pool_adapter.owned.OwnedAccount → M (core.result.Result (Slice U8) solana_program_error.ProgramError)

abbrev AuthCall (M : Type → Type) := solana_pubkey.Pubkey →
 Slice r1_pool_adapter.owned.OwnedAccount → solana_pubkey.Pubkey → U8 → U64 →
 M (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts solana_program_error.ProgramError)
'''
source=(E/'NMS_EmittedValidate.lean').read_text();body=source[source.index('def validate '):source.rindex('end NMS_Emitted')]
body=body.replace('def validate (ops : Ops) (auth : AuthCall)','def validate (ops : Ops) (effects : Effects M) (auth : AuthCall M)')
body=body.replace('  Result (core.result.Result r1_pool_adapter.ValidatedAsqa','  M (core.result.Result r1_pool_adapter.ValidatedAsqa')
for n in selected:body=body.replace(f'ops.op{n} ',f'effects.op{n} ').replace(f'ops.op{n}\n',f'effects.op{n}\n')
body=body.replace('ops.op45','effects.op45').replace('(get ops)','effects.data')
s+='\n'+body
s+='\ndef raw (ops : Ops) : Effects Result := {\n'+''.join(f' op{n} := ops.op{n}\n' for n in selected)+' data := NMS_Emitted.get ops\n}\n'
s+='''
theorem erases (ops : Ops) (auth : NMS_Emitted.AuthCall)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 validate ops (raw ops) auth program accounts data slot =
 NMS_Emitted.validate ops auth program accounts data slot := by
 unfold validate raw NMS_Emitted.validate
 rfl
#print axioms erases
end NMS_Effect242
'''
(E/'NMS_Effect242.lean').write_text(s)
s='''import NMS_Effect242
set_option autoImplicit false
noncomputable section
namespace NMS_Effect241
open Aeneas Aeneas.Std Result AdapterRw
variable {M : Type → Type} [Monad M] [MonadLift Result M]
local instance : MonadLift Result Result where
 monadLift := id
structure Effects (M : Type → Type) where
'''
for n in [11,22,44,53]:
 field=fields[n]
 if n==11: field=field.replace('→ Result\n        (core.result.Result Unit', '→ M\n        (core.result.Result Unit')
 else: field=re.sub(r'(?<!\.)\bResult\b','M',field)
 s+=field
s+='''  validate : solana_pubkey.Pubkey → Slice r1_pool_adapter.owned.OwnedAccount → Slice U8 →
   core.result.Result U64 solana_program_error.ProgramError → M (core.result.Result r1_pool_adapter.ValidatedAsqa solana_program_error.ProgramError)
  data : r1_pool_adapter.owned.OwnedAccount → M (core.result.Result (Slice U8) solana_program_error.ProgramError)

/-- Full error callback, evaluated only on the actual Err arm. -/
def mapError {A : Type} (reply : core.result.Result A aspis_r1_cost_probe.verifier.Error)
 (callback : aspis_r1_cost_probe.verifier.Error → M solana_program_error.ProgramError) :
 M (core.result.Result A solana_program_error.ProgramError) :=
 match reply with
 | .Ok a => pure (.Ok a)
 | .Err e => do
   let error ← callback e
   pure (.Err error)
'''
source=(E/'NMS_Emitted241.lean').read_text();body=source[source.index('def stage2 '):source.rindex('end NMS_Emitted')]
body=body.replace('def stage2 (ops : Ops) (auth : AuthCall)','def stage2 (ops : Ops) (effects : Effects M)')
body=body.replace('  Result (core.result.Result Unit solana_program_error.ProgramError)','  M (core.result.Result Unit solana_program_error.ProgramError)',1)
body=body.replace('validate ops auth','effects.validate').replace('(get ops)','effects.data')
for n in [11,22,53]:body=re.sub(r'\bops\.op'+str(n)+r'\b','effects.op'+str(n),body)
old='''core.result.Result.map_err (BuiltinFnOnce
                        aspis_r1_cost_probe.verifier.Error
                        solana_program_error.ProgramError) r6 (ops.op44)'''
assert old in body
body=body.replace(old,'mapError r6 effects.op44')
s+='\n'+body
s+='\ndef raw (ops : Ops) (auth : NMS_Emitted.AuthCall) : Effects Result := {\n'+''.join(f' op{n} := ops.op{n}\n' for n in [11,22,44,53])+' validate := NMS_Emitted.validate ops auth\n data := NMS_Emitted.get ops\n}\n'
s+='''
theorem mapError_raw {A : Type} (reply : core.result.Result A aspis_r1_cost_probe.verifier.Error)
 (callback : aspis_r1_cost_probe.verifier.Error → Result solana_program_error.ProgramError) :
 mapError reply callback = core.result.Result.map_err
  (BuiltinFnOnce aspis_r1_cost_probe.verifier.Error solana_program_error.ProgramError) reply callback := by
 cases reply <;> rfl
#print axioms mapError_raw

theorem erases (ops : Ops) (auth : NMS_Emitted.AuthCall)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 stage2 ops (raw ops auth) program accounts data slot =
 NMS_Emitted.stage2 ops auth program accounts data slot := by
 unfold stage2 raw NMS_Emitted.stage2
 simp only [mapError_raw]
 rfl
#print axioms erases
end NMS_Effect241
'''
(E/'NMS_Effect241.lean').write_text(s)
