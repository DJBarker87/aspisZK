import NGM_FinishControl
import NGM_FinishDomain
import NHE_Round
import NHE_DotDeployed
set_option autoImplicit false
noncomputable section
namespace NHQ_FinishRelationModel
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeFinishBody NGM_FinishControl
variable {W : Type}

def afterDotReply (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (reply : R E) : Result (R Unit) := do
 let cf4 ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf4 with
 | core.ops.control_flow.ControlFlow.Continue val4 =>
   ops.op0 17#u16 0#usize val4
   ops.op0 17#u16 1#usize a.rhs
   if a.next != 22#usize
   then ok (core.result.Result.Err verifier.Error.Query)
   else
     let b1 ←
       ops.ne
         val4 a.rhs
     if b1
     then ok (core.result.Result.Err verifier.Error.Query)
     else
       ops.op1 obs verifier.Phase.Final
       ok (core.result.Result.Ok ())
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Unit (core.convert.FromSame verifier.Error) residual

def afterPairReply (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) (claim : E)
 (reply : R E) : Result (R Unit) := do
 let cf3 ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf3 with
 | core.ops.control_flow.ControlFlow.Continue val3 =>
   ops.op0 16#u16 0#usize val3
   ops.op0 16#u16 1#usize claim
   let b ←
     ops.ne
       val3 claim
   if b
   then ok (core.result.Result.Err verifier.Error.Relation)
   else
     ops.op1 obs verifier.Phase.Relation
     let s1 := alloc.vec.Vec.deref a.weights
     let r4 ← ops.op4 v.final_message s1
     afterDotReply ops v p a obs r4
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Unit (core.convert.FromSame verifier.Error) residual

def afterWeightsReply (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) (folds : Usize) (claim : E)
 (reply : R W) : Result (R Unit) := do
 let cf2 ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf2 with
 | core.ops.control_flow.ControlFlow.Continue val2 =>
   let s ←
     core.array.Array.index (core.ops.index.IndexSlice
       (core.slice.index.SliceIndexRangeToUsizeSlice
       aspis_core.field.wide_exact.WideExact)) p.alpha { «end» := folds }
   let r3 ← ops.op2 val2 s v.final_message p.kappa
   afterPairReply ops v p a obs claim r3
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Unit (core.convert.FromSame verifier.Error) residual

def afterRoundReply (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) (folds : Usize)
 (reply : R E) : Result (R Unit) := do
 let cf1 ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf1 with
 | core.ops.control_flow.ControlFlow.Continue val1 =>
   let r2 ← ops.op3 p.variant p.semantic_alpha p.z
   afterWeightsReply ops v p a obs folds val1 r2
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Unit (core.convert.FromSame verifier.Error) residual

def afterRound0 (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (reply : R E) : Result (R Unit) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf with
 | core.ops.control_flow.ControlFlow.Continue val =>
   let i ← ops.op6 p.variant
   if i = 2#usize
   then
     let we1 ← Array.index_usize p.alpha 1#usize
     let r1 ← ops.op5 v.round1 we1 val 1#usize
     afterRoundReply ops v p a obs i r1
   else
     let r1 ← ops.op3 p.variant p.semantic_alpha p.z
     let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
     match cf1 with
     | core.ops.control_flow.ControlFlow.Continue val1 =>
       let s ←
         core.array.Array.index (core.ops.index.IndexSlice
           (core.slice.index.SliceIndexRangeToUsizeSlice
           aspis_core.field.wide_exact.WideExact)) p.alpha { «end» := i }
       let r2 ← ops.op2 val1 s v.final_message p.kappa
       let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
       match cf2 with
       | core.ops.control_flow.ControlFlow.Continue val2 =>
         ops.op0 16#u16 0#usize val2
         ops.op0 16#u16 1#usize val
         let b ←
           ops.ne
             val2 val
         if b
         then ok (core.result.Result.Err verifier.Error.Relation)
         else
           ops.op1 obs verifier.Phase.Relation
           let s1 := alloc.vec.Vec.deref a.weights
           let r3 ← ops.op4 v.final_message s1
           let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
           match cf3 with
           | core.ops.control_flow.ControlFlow.Continue val3 =>
             ops.op0 17#u16 0#usize val3
             ops.op0 17#u16 1#usize a.rhs
             if a.next != 22#usize
             then ok (core.result.Result.Err verifier.Error.Query)
             else
               let b1 ←
                 ops.ne
                   val3 a.rhs
               if b1
               then ok (core.result.Result.Err verifier.Error.Query)
               else
                 ops.op1 obs verifier.Phase.Final
                 ok (core.result.Result.Ok ())
           | core.ops.control_flow.ControlFlow.Break residual =>
             core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
               Unit (core.convert.FromSame verifier.Error) residual
       | core.ops.control_flow.ControlFlow.Break residual =>
         core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
           Unit (core.convert.FromSame verifier.Error) residual
     | core.ops.control_flow.ControlFlow.Break residual =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         Unit (core.convert.FromSame verifier.Error) residual
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Unit (core.convert.FromSame verifier.Error) residual



def staged (ops : Ops W)
  (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result Unit verifier.Error)
  := do
  let we ← Array.index_usize p.alpha 0#usize
  let r ← ops.op5 v.round0 we p.claim 0#usize
  afterRound0 ops v p a obs r
theorem source (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) :
 Port3_NativeFinishBody.verifier.finish_relation ops v p a obs = staged ops v p a obs := by rfl

/-- The pair law's required interface is the full Result on the SAME W/alpha/message/kappa.
It is not a premise that pair succeeds or equals claim. -/
theorem pair_stage (ops : Ops W) (v : verifier.View) (a : verifier.Accumulator)
 (obs : Option (verifier.Phase → Result Unit)) (claim : E)
 (weights : W) (alpha : Slice E) (kappa : E) (packet : Result (R E))
 (NHM_pair : ops.op2 weights alpha v.final_message kappa = packet) :
 bindChild (ops.op2 weights alpha v.final_message kappa) (afterPair ops v a obs claim) =
 bindChild packet (afterPair ops v a obs claim) := by rw [NHM_pair]

theorem child_error {A B : Type} (error : verifier.Error) (next : A → Result (R B)) :
 bindChild (ok (.Err error)) next = ok (.Err error) := by rfl

theorem child_fail {A B : Type} (error : Aeneas.Std.Error) (next : A → Result (R B)) :
 bindChild (.fail error) next = .fail error := by rfl

theorem child_div {A B : Type} (next : A → Result (R B)) :
 bindChild .div next = .div := by rfl

#print axioms source
#print axioms pair_stage
#print axioms child_error
#print axioms child_fail
#print axioms child_div
end NHQ_FinishRelationModel
