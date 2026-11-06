import NKG_LowFrame
import NKG_PreparedRaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_PreludeFrame
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP)
open FIw_ArrayValue (canonical)
open FJh_Base (State cell)
open FJa_PoseidonOrigins (Openings Selectors)
open NKG_OracleCuts (Three Prepared Packed)
open NKG_InternalChoices (get_ok)
structure Observation where
 leadingLow : NQ
 fullStates : Nat → NQ
 internalStates : Nat → NQ
 prepared : Prepared
 block : NP
 leading : Packed
 full : Packed
 internal : State
 prepareArgs : Array NQ 4#usize
 prepareCalls : Nat
 openingArg : Openings
 fullStateArg : State
 fullLocalArg : State
 internalStateArg : State
 internalLocalArg : State
 prefixCalls : Nat
def weights (o : Observation) : Three := Array.make 3#usize [o.leadingLow,o.fullStates 3,o.internalStates 7]
/-- Literal read, two finite one-step fold traces, original three child calls,
and the four constructor replies. Every clause is a named native cut. -/
structure Cut (o : Openings) (s : Selectors) (n : Observation) : Prop where
 leadingRead : n.leadingLow=cell s.local ⟨0,by decide⟩
 fullTrace : NKG_LowFrame.Trace s NKG_LowFrame.fullRows n.fullStates
 internalTrace : NKG_LowFrame.Trace s NKG_LowFrame.internalRows n.internalStates
 branches : NKG_OracleCuts.Prefix o s n.openingArg n.fullStateArg n.fullLocalArg n.internalStateArg n.internalLocalArg
   (NKG_OracleChoices.leading o) (NKG_OracleChoices.full o s) n.leading n.full
   (NKG_OracleChoices.internal o s) n.internal n.prefixCalls
 prepares : NKG_OracleCuts.Prepare (weights n) s.block n.prepareArgs
   (NKG_PreparedRaw.replies (weights n) s.block) n.prepared n.block n.prepareCalls
/-- Low values feed THIS constructor map; all returned branch/cache carriers
are the SAME values consumed by the subsequent group cuts. -/
theorem result (o : Openings) (s : Selectors) (n : Observation)
 (hz : canonical o.z) (hx : canonical o.xor12_z) (hs : canonical s.local) (hb : Canon s.block)
 (cut : Cut o s n) :
 n.prepared=NKG_OracleChoices.prepared s ∧ n.block=NKG_OracleChoices.block s ∧
 n.leading=NKG_OracleChoices.leading o ∧ n.full=NKG_OracleChoices.full o s ∧
 n.internal=NKG_OracleChoices.internal o s := by
 have r0 : Array.index_usize s.local 0#usize=ok n.leadingLow := by
   rw [cut.leadingRead]
   exact RawPoseidonExternalRowReads.array_index_usize_ok s.local 0#usize (by decide)
 have v0 : NKG_OracleChoices.leadingLow s=n.leadingLow := get_ok _ _ _ r0
 have vf : NKG_OracleChoices.fullLow s=n.fullStates 3 := get_ok _ _ _ (NKG_LowFrame.full s n.fullStates hs cut.fullTrace).1
 have vi : NKG_OracleChoices.internalLow s=n.internalStates 7 := get_ok _ _ _ (NKG_LowFrame.internal s n.internalStates hs cut.internalTrace).1
 have vw : weights n=NKG_OracleChoices.weights s :=
   (congrArg₂ (fun a b=>Array.make 3#usize [a,b,n.internalStates 7]) v0.symm vf.symm).trans
     (congrArg (fun c=>Array.make 3#usize [NKG_OracleChoices.leadingLow s,NKG_OracleChoices.fullLow s,c]) vi.symm)
 have ready := NKG_OracleChoices.ready o s hz hx hs hb
 have native := NKG_PreparedRaw.native (weights n) s.block n.prepareArgs n.prepared n.block n.prepareCalls cut.prepares
 have pmodel := NKG_PreparedRaw.source (NKG_OracleChoices.weights s) (NKG_OracleChoices.prepared s) ready.preparedCall
 have pvalue : n.prepared=NKG_OracleChoices.prepared s :=
   native.1.trans ((congrArg NKG_PreparedRaw.model vw).trans pmodel.symm)
 exact ⟨pvalue,native.2,cut.branches.leadingReturn,cut.branches.fullReturn,cut.branches.internalReturn⟩
#print result
#print axioms result
#print Cut
end AspisR1.NKG_PreludeFrame
end
