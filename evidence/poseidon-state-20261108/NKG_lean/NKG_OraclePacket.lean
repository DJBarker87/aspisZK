import NKG_PreludeFrame
import NKG_BuilderRaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_OraclePacket
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings Selectors)
open NKG_OracleCuts (Packed)
def outputs (groups : Fin 4 → NKG_GroupFrame.Observation) : Packed :=
 ⟨List.ofFn (fun i : Fin (4#usize).val=>(groups ⟨i.val,i.isLt⟩).out),by simp⟩
/-- Complete TX1:308 packet. Hypotheses are its original canonical input
carrier and the reviewed native parent cuts only. The prelude is chained to
all groups on SAME raw values, every field child is internally discharged,
and the actual four-array constructor supplies the final native carrier. -/
theorem source (o : Openings) (s : Selectors) (nativeOut : Packed)
 (pre : NKG_PreludeFrame.Observation) (groups : Fin 4 → NKG_GroupFrame.Observation)
 (indices : Fin 4 → Nat) (outputCalls : Nat)
 (hz : canonical o.z) (ht : canonical o.succ_z) (hx : canonical o.xor12_z)
 (hs : canonical s.local) (hb : Canon s.block)
 (precut : NKG_PreludeFrame.Cut o s pre)
 (groupcuts : ∀ g,NKG_GroupFrame.Frame o.succ_z pre.internal pre.leading pre.full pre.prepared pre.block g (groups g))
 (outputcut : NKG_OracleCuts.Output (outputs groups) nativeOut indices outputCalls) :
 state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=ok nativeOut ∧ canonical nativeOut ∧
 decoded nativeOut=fun g=>R0P.poseidonPackingFormula
   ExtractedMaskQmPackBase4Arithmetic.iBasis ExtractedMaskQmPackBase4Arithmetic.uBasis
   (fun j=>R0P.poseidonScalarResidual (FJh_Native07RawValue.openings o)
     (decode s.block) (decoded s.local) (FJe_ExternalAdjoint.lane g j)) := by
 obtain ⟨pp,pb,pl,pf,pi⟩ := NKG_PreludeFrame.result o s pre hz hx hs hb precut
 have ready := NKG_OracleChoices.ready o s hz hx hs hb
 have groupRaw (g : Fin 4) : (groups g).out=NKG_BuilderRaw.reply (NKG_OracleChoices.capture o s) (NKG_GroupFrame.index g) := by
   have cut : NKG_GroupFrame.Frame o.succ_z (NKG_OracleChoices.internal o s)
     (NKG_OracleChoices.leading o) (NKG_OracleChoices.full o s) (NKG_OracleChoices.prepared s)
     (NKG_OracleChoices.block s) g (groups g) := by
     simpa only [pp,pb,pl,pf,pi] using groupcuts g
   obtain ⟨out,called,_⟩ := NKG_CellTotal.cell o (NKG_OracleChoices.internal o s) s.block
     (NKG_OracleChoices.block s) (NKG_OracleChoices.prepared s) (NKG_OracleChoices.leading o)
     (NKG_OracleChoices.full o s) (NKG_OracleChoices.weights s) (NKG_GroupFrame.index g) g.isLt
     ht ready.internalCanonical hb ready.leadingCanonical ready.fullCanonical ready.weightsCanonical
     ready.preparedCall ready.blockCall
   have frame := NKG_GroupFrame.result o.succ_z (NKG_OracleChoices.internal o s)
     (NKG_OracleChoices.leading o) (NKG_OracleChoices.full o s) (NKG_OracleChoices.prepared s)
     (NKG_OracleChoices.block s) g (groups g) cut
   have raw := NKG_GroupRaw.value o (NKG_OracleChoices.internal o s) (NKG_OracleChoices.block s)
     (NKG_OracleChoices.prepared s) (NKG_OracleChoices.leading o) (NKG_OracleChoices.full o s)
     g out (NKG_OracleChoices.capture o s) ht ready.internalCanonical called
   exact frame.trans (raw.trans (NKG_BuilderRaw.reply_ok (NKG_OracleChoices.capture o s)
     (NKG_GroupFrame.index g) out (NKG_OracleChoices.capture o s) called).symm)
 have values : outputs groups=NKG_BuilderRaw.values (NKG_OracleChoices.capture o s) := by
   apply Subtype.ext
   apply List.ext_getElem
   · rw [(outputs groups).property,(NKG_BuilderRaw.values (NKG_OracleChoices.capture o s)).property]
   · intro j hj hk
     have h4 : j<4 := by simpa [(outputs groups).property] using hj
     simpa only [outputs,NKG_BuilderRaw.values,List.getElem_ofFn] using groupRaw ⟨j,h4⟩
 obtain ⟨out,run,co,value⟩ := NKG_OracleSource.result o s hz ht hx hs hb
 have builder := NKG_OracleChoices.builder o s out run
 have sourceValues := NKG_BuilderRaw.source (NKG_OracleChoices.capture o s) out builder
 have same : nativeOut=out := outputcut.returned.trans (values.trans sourceValues.symm)
 rw [same]
 exact ⟨run,co,value⟩
#print source
#print axioms source
end AspisR1.NKG_OraclePacket
end
