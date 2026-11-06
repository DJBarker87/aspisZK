import NKG_OracleFactor
import NKG_LowTotal
import NKG_PreparedMap
import NKG_CellTotal
import NKG_FullSource
import NKG_InternalSource
import NIH_Leading
import RPv_FJk_Native07Value
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_OracleSource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIv_PreparedNew (NP)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings Selectors)
/-- Complete emitted deterministic evaluator and adopted scalar residual, on
SAME openings, selector array and block. Every entered child domain is derived
internally. No child-success, output, oracle-value or arbitrary Ops premise. -/
theorem result (o : Openings) (s : Selectors)
 (hz : canonical o.z) (ht : canonical o.succ_z) (hx : canonical o.xor12_z)
 (hs : canonical s.local) (hb : Canon s.block) :
 ∃ out,state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=ok out ∧
 canonical out ∧ decoded out=fun g=>R0P.poseidonPackingFormula
   ExtractedMaskQmPackBase4Arithmetic.iBasis ExtractedMaskQmPackBase4Arithmetic.uBasis
   (fun j=>R0P.poseidonScalarResidual (FJh_Native07RawValue.openings o)
     (decode s.block) (decoded s.local) (FJe_ExternalAdjoint.lane g j)) := by
 obtain ⟨leadingLow,r0,c0⟩ := JFy_ArrayTotal.read s.local 0#usize (by decide) hs
 obtain ⟨fullLow,rlf,clf⟩ := NKG_LowTotal.full s hs
 obtain ⟨internalLow,rli,cli⟩ := NKG_LowTotal.internal s hs
 obtain ⟨lead,rlead,clead,_⟩ := NIH_Leading.result o hz hx
 obtain ⟨full,rfull,cfull,_⟩ := NKG_FullSource.result o.z s.local hz hs
 obtain ⟨internal,rinternal,cinternal,_⟩ := NKG_InternalSource.result o.z s.local hz hs
 let w : Array NQ 3#usize := Array.make 3#usize [leadingLow,fullLow,internalLow]
 have cw : canonical w := by
   intro x hx
   simp only [w,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
   rcases hx with rfl|rfl|rfl
   · exact c0
   · exact clf
   · exact cli
 obtain ⟨p,rp⟩ := NKG_PreparedMap.result w cw
 obtain ⟨block,rb,_⟩ := FIv_PreparedNewTotal.value s.block hb
 obtain ⟨out,rout,cout⟩ := NKG_CellTotal.array o internal s.block block p lead full w
   ht cinternal hb clead cfull cw rp rb
 dsimp only [w] at rp
 have run : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=ok out := by
   rw [NKG_OracleFactor.factor]
   simp only [NKG_OracleFactor.source,r0,rlf,rli,rlead,rfull,rinternal,rp,rb,rout,bind_tc_ok]
 exact ⟨out,run,FJk_Native07Value.value o s out hz ht hx hs hb run⟩
#print result
#print axioms result
end AspisR1.NKG_OracleSource
end
