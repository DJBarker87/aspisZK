import JGx_SdkEncoded
import JGx_SdkConstants
import NDO_JGx_ProofAccount
import NDO_JGx_PublicArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_SdkEncodedTail
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.publicInput JFx_NativeBytes.checkpoint

theorem source (ops : Ops) (validated : r1_pool_adapter.ValidatedAsqa) (headerBytes : Array U8 688#usize)
    (common : ops.op19=ok 1520#usize)
    (verifier : ops.op11 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      JFx_NativeBytes.publicInput JFx_NativeBytes.proof JFx_NativeBytes.checkpoint () none=ok (.Ok ())) :
    JGx_SdkEncoded.afterEncoded ops validated (JGx_ProofAccount.value headerBytes)
      JFx_NativeBytes.checkpoint JGx_PublicArray.value=ops.op53 validated.statement := by
  unfold JGx_SdkEncoded.afterEncoded
  simp only [lift,bind_tc_ok]
  rw [JGx_PublicArray.length,JGx_SdkConstants.statementSize ops common,bind_tc_ok]
  simp only [show (1880#usize !=1880#usize)=false from by decide,Bool.false_eq_true,ite_false]
  rw [JGx_ProofAccount.suffix,bind_tc_ok,JGx_SdkConstants.observer,bind_tc_ok,JGx_PublicArray.source,verifier,bind_tc_ok]
  simp only [core.result.Result.map_err,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
#print axioms source
end AspisR1.JGx_SdkEncodedTail
end
