import NKU_AfterZSource
set_option autoImplicit false
noncomputable section
namespace NKU_TailSource
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
/-- Verbatim native emitted suffix after power43, split from the failed
L057 whole semantic factor; only parameter names and S2 are substituted. -/
def native {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : NKU.E) (val4 : NKU.K)
 (queryValues : Array U32 22#usize) (semantic_alpha : Array NKU.K 10#usize)
 (val6 val7 val8 val9 : NKU.K) (val10 val11 : NKU.E) (val12 : NKU.K) (r50 : verifier.Reader) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let i30 ←
   CheckpointBytes4Ops.finalLen (NIL_Carriers.variant transport.Variant.S2)
 let q ←
   (ok (NIL_Carriers.unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))
 let r51 ←
   (recordFilled s.frame.reservation)
     (aspis_core.field.QM31.Insts.CoreMarkerCopy (fun x=>ok x))
     i30 q
 let r52 ←
   NIL_FreshOps.mapError
     (verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
     (NIL_FreshOps.digest d))
     r51 ()
 let cf14 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r52
 match cf14 with
 |
   core.ops.control_flow.ControlFlow.Continue
   val13 =>
   let r53 ←
     recordWeights
       s.frame.checkpoint r50.«at» val13
   let cf15 ←
     core.result.Result.Insts.CoreOpsTry.branch
       r53
   match cf15 with
   |
     core.ops.control_flow.ControlFlow.Continue
     val14 =>
     let (weights, at2) := val14
     if at2 != end1
     then
       ok
         (core.result.Result.Err
         verifier.Error.Checkpoint)
     else
       let i31 ←
         lift (UScalar.cast
           .Usize i4)
       ok (core.result.Result.Ok
         ({
            variant := .S2,
            roots :=
              (Array.make
                 2#usize [
                a3, a4
                ]),
            gamma := val,
            kappa := val1,
            alpha :=
              (Array.make
                 2#usize [
                val2, val3
                ]),
            rho := val4,
            queries :=
              queryValues,
            semantic_alpha,
            z :=
              (Array.make
                 2#usize [
                {
                  x := val6,
                  y := val7
                },
                {
                  x := val8,
                  y := val9
                }
                ]),
            claim := val10,
            state
          },
         {
           weights,
           rhs := val11,
           power := val12,
           next := i31
         }))
   |
     core.ops.control_flow.ControlFlow.Break
     residual =>
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       (verifier.Prepared ×
       verifier.Accumulator)
       (core.convert.FromSame
       verifier.Error) residual
 |
   core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (verifier.Prepared ×
     verifier.Accumulator)
     (core.convert.FromSame
     verifier.Error) residual

theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : NKU.E) (val4 : NKU.K)
 (queryValues : Array U32 22#usize) (semantic_alpha : Array NKU.K 10#usize)
 (val6 val7 val8 val9 : NKU.K) (val10 val11 : NKU.E) (val12 : NKU.K) (r50 : verifier.Reader) : native d s i4 end1 state a3 a4 val val1 val2 val3 val4 queryValues semantic_alpha val6 val7 val8 val9 val10 val11 val12 r50=NKU_AfterZSource.run d s i4 end1 state a3 a4 val val1 val2 val3 val4 queryValues semantic_alpha val6 val7 val8 val9 val10 val11 val12 r50 := by
 unfold native NKU_AfterZSource.run NKK_AllocationStage.source NKK_Try.emitted
 simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_LogReduce.lift_ok_bind,CheckpointBytes4Ops.finalLen,NIL_Carriers.variant]
 repeat' first
 | rfl
 | (apply NKK_LogAlgebra.bind_congr;intro value)
 | split
 | (fail_if_no_progress simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_LogReduce.lift_ok_bind,NJU_Log.prod_cases])
#print axioms source
end NKU_TailSource
