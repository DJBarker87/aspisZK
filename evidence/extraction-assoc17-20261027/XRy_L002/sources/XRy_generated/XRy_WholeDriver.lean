import XRw_GenericDriver
import XRw_PairedStep
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRy_WholeDriver
open XRv_QueryDriver XRv_QueryDriverTotal
open Query31ExplicitListLoop Query31ExplicitScanBody
open XRo_Join_Carriers
abbrev CE := AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError
abbrev RE := XRn_Join_Release.aspis_core.transcript.QuerySampleError
abbrev Out := core.result.Result (Array U32 22#usize × Block) CE

def error : RE → CE
 | .BoundNotPowerOfTwo b => .BoundNotPowerOfTwo b
 | .CountExceedsBound n b => .CountExceedsBound n b
 | .DrawLimitExhausted n m => .DrawLimitExhausted n m

def finish (s : Query31ExplicitScanBody.CurrentScan) (advance : Block) : Result Out := do
 let r ← AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish s
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | core.ops.control_flow.ControlFlow.Continue val => ok (.Ok (val,advance))
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (Array U32 22#usize × Block) (core.convert.FromSame CE) residual

theorem finish_same (s : Query31ExplicitScanBody.CurrentScan) (valid : validState s)
 (stop : Bool) (advance : Block) :
 mapR (inner id error)
   (XRv_QueryDriver.finish (s.accepted.val.take s.accepted_len.val,s.draws.val,stop,advance)) =
 finish s advance := by
 have hlen : (s.accepted.val.take s.accepted_len.val).length = s.accepted_len.val := by
   simpa only [acceptedPrefix,List.length_map] using valid.2.2
 have hround : XRn_Join_usize s.accepted_len.val = s.accepted_len := by
   apply UScalar.eq_of_val_eq
   change s.accepted_len.val % (UScalar.cMax .Usize+1) = s.accepted_len.val
   apply Nat.mod_eq_of_lt
   scalar_tac
 by_cases hs : s.accepted_len = 22#usize
 · have hv : s.accepted_len.val = 22 := congrArg UScalar.val hs
   have ht : s.accepted.val.take s.accepted_len.val = s.accepted.val := by
     apply List.take_of_length_le
     have ha : s.accepted.val.length = 22 := s.accepted.property
     omega
   simp only [XRv_QueryDriver.finish,hlen,hv,↓reduceDIte,mapR,bind_tc_ok,XRo_Join_Carriers.inner,id,
     finish,AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish,
     AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT,
     AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_MAX_DRAWS,hs,↓reduceIte,
     core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
   apply congrArg (fun a : Array U32 22#usize =>
     (Result.ok (core.result.Result.Ok (a,advance)) : Result Out))
   apply Subtype.ext
   simpa only [hv] using ht
 · have hv : s.accepted_len.val ≠ 22 := by
     intro h
     apply hs
     apply UScalar.eq_of_val_eq
     exact h
   simp only [XRv_QueryDriver.finish,hlen,hv,↓reduceDIte,mapR,bind_tc_ok,XRo_Join_Carriers.inner,error,
     finish,AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish,
     AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT,
     AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_MAX_DRAWS,hs,↓reduceIte,
     core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
     core.convert.FromSame,core.convert.FromSame.from,hround]

def run (blocks advances : Blocks) : List Nat → Query31ExplicitScanBody.CurrentScan → Block → Result Out
 | [],s,old => finish s old
 | i::rest,s,_ => do
   let block ← Array.index_usize blocks (XRn_Join_usize i)
   let (stop,sf) ← Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords s block
   let advance ← Array.index_usize advances (XRn_Join_usize i)
   if stop then finish sf advance else run blocks advances rest sf advance

theorem fold_same (blocks advances : Blocks) (indices : List Nat)
 (bounded : ∀ i ∈ indices, i<8) (s : Query31ExplicitScanBody.CurrentScan) (valid : validState s) (old : Block) :
 mapR (inner id error)
   ((indices.foldlM (step blocks advances)
     (s.accepted.val.take s.accepted_len.val,s.draws.val,false,old)) >>= XRv_QueryDriver.finish) =
 run blocks advances indices s old := by
 induction indices generalizing s old with
 | nil => exact finish_same s valid false old
 | cons i rest ih =>
   have hi : i<8 := bounded i (by simp)
   obtain ⟨sf,pending,advance,ha,hr,he,hv⟩ := XRw_PairedStep.same_step blocks advances i hi s valid old
   rw [List.foldlM_cons,he,bind_tc_ok]
   unfold run
   rw [index blocks i hi,bind_tc_ok,hr,bind_tc_ok]
   simp only [ha,bind_tc_ok]
   cases hs : optionStop pending with
   | false =>
     simp only [hs,Bool.false_eq_true,↓reduceIte]
     exact ih (fun j hj => bounded j (List.mem_cons_of_mem i hj)) sf hv advance
   | true =>
     simp only [hs,↓reduceIte]
     rw [XRv_QueryDriver.stopped,bind_tc_ok]
     exact finish_same sf hv true advance

theorem guarded_step (blocks advances : Blocks) :
 XRw_GenericDriver.guarded (step blocks advances) (fun s : State => s.2.2.1) =
 step blocks advances := by
 funext s i
 rcases s with ⟨a,d,stop,old⟩
 cases stop <;> rfl

theorem raw_unrolled (blocks advances : Blocks) :
 aspis_core.r0_transcript.queries_from_pairs blocks advances =
 (XRw_GenericDriver.unrolled (step blocks advances) (fun s : State => s.2.2.1)
   (List.range 8) ([],0,false,advances.val[7]?.getD (Array.repeat 32#usize 0#u8)) >>=
   XRv_QueryDriver.finish) := by
 have h := XRw_GenericDriver.first_stop_fold
   (M:=Result) (fun (_ : State) (_ : State → Result State) => rfl)
   (step blocks advances) (fun s : State => s.2.2.1) XRv_QueryDriver.finish
   (List.range 8) ([],0,false,advances.val[7]?.getD (Array.repeat 32#usize 0#u8))
 rw [guarded_step] at h
 exact h.symm

-- The bounded array reads have no effects and succeed on the SAME arrays.
theorem run_unrolled (blocks advances : Blocks) (s : Query31ExplicitScanBody.CurrentScan) (old : Block) :
 run blocks advances (List.range 8) s old =
 AspisR1Query31Transcript.queries_from_pairs_with_scan
   (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
   s blocks advances := by
 change run blocks advances [0,1,2,3,4,5,6,7] s old = _
 unfold AspisR1Query31Transcript.queries_from_pairs_with_scan
 have hb0 := index blocks 0 (by omega)
 change Array.index_usize blocks 0#usize = _ at hb0
 have hb1 := index blocks 1 (by omega)
 change Array.index_usize blocks 1#usize = _ at hb1
 have hb2 := index blocks 2 (by omega)
 change Array.index_usize blocks 2#usize = _ at hb2
 have hb3 := index blocks 3 (by omega)
 change Array.index_usize blocks 3#usize = _ at hb3
 have hb4 := index blocks 4 (by omega)
 change Array.index_usize blocks 4#usize = _ at hb4
 have hb5 := index blocks 5 (by omega)
 change Array.index_usize blocks 5#usize = _ at hb5
 have hb6 := index blocks 6 (by omega)
 change Array.index_usize blocks 6#usize = _ at hb6
 have hb7 := index blocks 7 (by omega)
 change Array.index_usize blocks 7#usize = _ at hb7
 have ha0 := index advances 0 (by omega)
 change Array.index_usize advances 0#usize = _ at ha0
 have ha1 := index advances 1 (by omega)
 change Array.index_usize advances 1#usize = _ at ha1
 have ha2 := index advances 2 (by omega)
 change Array.index_usize advances 2#usize = _ at ha2
 have ha3 := index advances 3 (by omega)
 change Array.index_usize advances 3#usize = _ at ha3
 have ha4 := index advances 4 (by omega)
 change Array.index_usize advances 4#usize = _ at ha4
 have ha5 := index advances 5 (by omega)
 change Array.index_usize advances 5#usize = _ at ha5
 have ha6 := index advances 6 (by omega)
 change Array.index_usize advances 6#usize = _ at ha6
 have ha7 := index advances 7 (by omega)
 change Array.index_usize advances 7#usize = _ at ha7
 simp only [run,finish,
   index blocks 0 (by omega),index blocks 1 (by omega),index blocks 2 (by omega),
   index blocks 3 (by omega),index blocks 4 (by omega),index blocks 5 (by omega),
   index blocks 6 (by omega),index blocks 7 (by omega),
   index advances 0 (by omega),index advances 1 (by omega),index advances 2 (by omega),
   index advances 3 (by omega),index advances 4 (by omega),index advances 5 (by omega),
   index advances 6 (by omega),index advances 7 (by omega),
   hb0,hb1,hb2,hb3,hb4,hb5,hb6,hb7,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,bind_tc_ok,ite_self]
 try rfl

/-- Full eight-stage SAME-array equation, with complete first-stop finish/error
and selected advance state. No successful-driver hypothesis. -/
theorem whole (blocks advances : Blocks) :
 mapR (inner id error)
   (aspis_core.r0_transcript.queries_from_pairs blocks advances) =
 AspisR1Query31Transcript.queries_from_pairs_with_scan
   (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
   Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances := by
 rw [raw_unrolled]
 rw [XRw_GenericDriver.first_stop_fold
   (fun (_ : State) (_ : State → Result State) => rfl)]
 rw [guarded_step]
 have h := fold_same blocks advances (List.range 8) (fun i hi => List.mem_range.mp hi)
   Query31ConcreteDriverTraceFacts.sourceDefaultState
   Query31ConcreteDriverTraceFacts.sourceDefaultState_valid
   (advances.val[7]?.getD (Array.repeat 32#usize 0#u8))
 change mapR (inner id error)
   ((List.range 8).foldlM (step blocks advances)
     ([],0,false,advances.val[7]?.getD (Array.repeat 32#usize 0#u8)) >>= XRv_QueryDriver.finish) = _
 exact h.trans (run_unrolled blocks advances _ _)

#print axioms finish_same
#print axioms fold_same
#print axioms guarded_step
#print axioms raw_unrolled
#print axioms run_unrolled
#print axioms whole
end XRy_WholeDriver
