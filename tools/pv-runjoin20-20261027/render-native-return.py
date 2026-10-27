from pathlib import Path
import sys
L=Path(__file__).resolve().parents[2]/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PV_RunJoin_TransferPayload20
import R1Z.PV_RunJoin_WithdrawalPayload20
import R1Z.PV_RunJoin_SourceTransition20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeReturn20
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_FixtureArguments
local notation "E" => PV_RunJoin_ShippedExternal.E_shipped
local notation "R" => PV_RunJoin_CompilerDictionary16.shipped
'''
for k in ['transfer','withdrawal']:
 payload=f'PV_RunJoin_{k.capitalize()}Payload20.output'
 header=f'''(i : PV_Src_NativeInput.Input)
    (hr : i.request = {k}Request) (hw : i.witness = witness)
    (hc : i.change = {k}Change) (hl : i.laneAnchor = laneAnchor)
    (hs : i.snapshot = snapshot)'''
 s+=f'''theorem {k}_call {header} :
    @PV_Src_NativeInput.run E R i = ok (.Ok {payload}) := by
  unfold PV_Src_NativeInput.run
  rw [hr,hw,hc,hl,hs]
  exact PV_RunJoin_{k.capitalize()}Payload20.source
#print axioms {k}_call

/-- The same selected i is preserved. Output association is an explicit P
obligation; it is not obtained by replacing Input.compiled. -/
theorem {k}_selected_iff {header} :
    (@PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) ↔ i.compiled = {payload} := by
  constructor
  · intro h
    exact (core.result.Result.Ok.inj (Result.ok.inj (({k}_call i hr hw hc hl hs).symm.trans h))).symm
  · intro h
    rw [h]
    exact {k}_call i hr hw hc hl hs
#print axioms {k}_selected_iff

theorem {k}_transition {header}
    (hreturn : @PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) :
    PV_Src_NativeInput.transition i.compiled.public_statement = PV_RunJoin_Recorded{k.capitalize()}.transition := by
  have he := ({k}_selected_iff i hr hw hc hl hs).mp hreturn
  rw [he]
  exact PV_RunJoin_SourceTransition20.{k}
#print axioms {k}_transition

theorem {k}_public {header}
    (hreturn : @PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) :
    PV_Src_NativeInput.publicInput i = PV_RunJoin_Recorded{k.capitalize()}.publicInput := by
  unfold PV_Src_NativeInput.publicInput
  rw [hr]
  simp only [PV_RunJoin_FixtureArguments.{k}Request]
  rw [{k}_transition i hr hw hc hl hs hreturn]
  rfl
#print axioms {k}_public

theorem {k}_semantic {header}
    (hreturn : @PV_Src_NativeInput.run E R i = ok (.Ok i.compiled)) :
    i.compiled.semantic_c1.c1 = PV_RunJoin_SourceBanks19.{k}Bank.merged := by
  rw [({k}_selected_iff i hr hw hc hl hs).mp hreturn]
  rfl
#print axioms {k}_semantic
'''
s+='end R1Z.PV_RunJoin_NativeReturn20\n';p=L/'PV_RunJoin_NativeReturn20.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('same-i execution and precise payload-association equivalence; no Input constructed')
