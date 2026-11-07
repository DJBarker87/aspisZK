import NNH_064Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064WeakField
open Aeneas Aeneas.Std NNH_Libraries NNH_064Install
attribute [local instance] Classical.propDecidable

def w (pub proof ck : RSL.Bytes) : RSL.Spec (Except V0.VErr Unit) :=
 fun env => NNC_ObservedLaw.w (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()
  frame pub proof ck env

theorem fits (x : RSL.Bytes × RSL.Bytes × RSL.Bytes)
 (domain : RSL.TX2_241.Dom064 (RSL.TAS.lib V0 (fun _ _=>True) w) x) :
 LIBB_Tx2Auth.Fits x.1 x.2.1 x.2.2 := by
 obtain ⟨hp,hc,hu,_⟩ := domain
 refine ⟨?_,?_,?_⟩
 · have bound : 1880 ≤ Usize.max := by scalar_tac
   exact hu.trans bound
 · rw [hp]; scalar_tac
 · rw [hc]; scalar_tac

theorem weak : RSL.TAS.Refines064 V0 f064 (fun _ _=>True) w := by
 intro x env domain
 have h := fits x domain
 unfold f064
 rw [dif_pos h]
 let pu := LIB_Bytes.fromBytes x.1 h.1
 let pr := LIB_Bytes.fromBytes x.2.1 h.2.1
 let cp := LIB_Bytes.fromBytes x.2.2 h.2.2
 have len : pr.val.length=57607 := by
  have bytes := LIB_Bytes.bytes_from x.2.1 h.2.1
  have length := congrArg List.length bytes
  rw [LIB_Bytes.bytes,NMS_R2N_RSLScalars.bytes_length] at length
  exact length.trans domain.1
 have native := NNH_064Observe.weak env pu pr cp frame len
 simpa only [pu,pr,cp,LIB_Bytes.bytes_from] using native

theorem writeFree (pub proof ck : RSL.Bytes) : RSL.TAS.WriteFree (w pub proof ck) := by
 intro env o source cell bytes
 exact NNC_ObservedLaw.writeFree (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()
  frame pub proof ck env o source cell bytes
#print axioms fits
#print axioms weak
#print axioms writeFree
end AspisR1.NNH_064WeakField
