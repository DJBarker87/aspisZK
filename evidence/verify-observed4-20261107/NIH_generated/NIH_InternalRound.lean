import NIH_InternalTotal
import NDO_JGj_InternalRoundTotal
import RPv_FJh_InternalRoundValue
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_InternalRound
open FIv_NativeArithmetic (NQ)
/-- The pow5 intermediate and every later linear-layer domain are derived on
this SAME original state, with the full Result and adopted value. -/
theorem result (s : Array NQ 16#usize) (constant : NQ)
 (canonical : FIw_ArrayValue.canonical s) (cc : FIv_NativeValue.Canon constant) :
 ∃ out,FIq_Native.state_only_poseidon.internal_round s constant=ok out ∧
 FIw_ArrayValue.canonical out ∧ FIw_ArrayValue.decoded out=
 R0P.poseidonInternalRound (FIw_ArrayValue.decoded s) (FIv_NativeValue.decode constant) := by
 obtain ⟨out,run,_⟩:=JGj_InternalRoundTotal.source s constant canonical cc
 exact ⟨out,run,FJh_InternalRoundValue.value s out constant canonical cc run⟩
#print axioms result
end AspisR1.NIH_InternalRound
end
