import Lean
import NFN_PhaseTransport
import NFS_NEV_CtorNormalization

set_option autoImplicit false
noncomputable section
namespace NFS_NEV_CtorResults
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
open NEV_AccumulateRaw.NEV_Bindings

def mValue (word : U32) : RawE := fromCtorE (NEV_CodeFieldBridge.value word)
def qValue (q : RawQ) : RawE :=
 fromCtorE ⟨NFS_NEV_CtorNormalization.normalized (toCtorQ q),NEV_CodeFieldRaw.aspis_core.field.QM31.ZERO⟩
/-- Reuse constructor totality on all raw words; only the nominal output
carrier is different at this actual accumulation call site. -/
theorem m31 (word : U32) :
    NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 word=
      ok (mValue word) := by
  simp only [NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    NEV_CodeFieldBridge.total,bind_tc_ok,mValue]
theorem qm (q : RawQ) :
    NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.from_qm31 q=ok (qValue q) := by
  simp only [NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.from_qm31,
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.from_qm31,
    NFS_NEV_CtorNormalization.total,bind_tc_ok,qValue]
#print axioms m31
#print axioms qm
end NFS_NEV_CtorResults
end

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
