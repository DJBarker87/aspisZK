from pathlib import Path
import sys
L=Path(__file__).resolve().parents[2]/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for kind,mod in [('transfer','CompilerTotal20'),('withdrawal','CompilerWithdrawal20')]:
 s=f'''import R1Z.PV_RunJoin_{mod}
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_{kind.capitalize()}Payload20
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1 pair_forest_copy_builder
open PV_RunJoin_FixtureArguments PV_RunJoin_ReferenceFixtureResults
local instance : ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : Records := PV_RunJoin_CompilerDictionary16.shipped
'''
 out=600 if kind=='transfer' else 250;variant='PrivateTransfer' if kind=='transfer' else 'Withdrawal';pub='PV_RunJoin_Recorded'+kind.capitalize()+'.publicRecord';bank=f'PV_RunJoin_SourceBanks19.{kind}Bank';pair=f'PV_RunJoin_AppendNative17.{kind}0';root=f'PV_RunJoin_AppendNative17.{kind}20'
 outputs=f'pair_trace.PoolV1PairTracePublicOutputsV1.{variant} {pub}.anchor_root {pub}.nullifier '
 if kind=='transfer':outputs+=pub+'.recipient_commitment '
 outputs+=f'{pub}.change_commitment {pair}'
 s+=f'''def output : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 := {{
  trace := {{
    stable := {{c1 := {bank}.stable}},late := {bank}.late,
    variant := pair_trace.PoolV1PairTraceVariantV1.{variant},
    private_directions := BuilderRecordsPath.bits (PV_Src_NativeDirections.reference witness),
    value_bits := Array.make 3#usize [PV_RunJoin_ValueBits20.bits witness.pair.value,
      PV_RunJoin_ValueBits20.bits {out}#u32,PV_RunJoin_ValueBits20.bits {kind}Change.value],
    public_outputs := {outputs},
    afterstate := PV_RunJoin_LateAppend18.result {pair} {root} }},
  semantic_c1 := {{c1 := {bank}.merged}},
  public_statement := ⟨snapshot,PV_RunJoin_LateAppend18.result {pair} {root}⟩ }}

theorem source : PV_RunJoin_{mod}.{kind}Call = ok (.Ok output) := by
'''
 original=(L/f'PV_RunJoin_{mod}.lean').read_text();body=original.split(f'\ntheorem {kind} :')[1].split(' := by\n',1)[1].split(f'\n#print axioms {kind}')[0];body=body.replace(f'unfold {kind}Call',f'unfold PV_RunJoin_{mod}.{kind}Call');body=body.replace('  exact ⟨_,rfl,rfl⟩','  rfl');s+=body+'\n#print axioms source\n'
 s+=f'''theorem semantic : output.semantic_c1.c1 = {bank}.merged := rfl
#print axioms semantic
end R1Z.PV_RunJoin_{kind.capitalize()}Payload20
'''
 p=L/f'PV_RunJoin_{kind.capitalize()}Payload20.lean'
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
print('explicit outputs only; no replacement native Input is constructed')
