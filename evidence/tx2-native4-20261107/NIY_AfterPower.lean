import NIY_AfterRhs
set_option autoImplicit false
noncomputable section
namespace NIY_AfterPower
open Aeneas Aeneas.Std Result ControlFlow Error NID_ResumeEmission

def suffix (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (val2 : aspis_core.field.wide_exact.WideExact) (val3 : aspis_core.field.wide_exact.WideExact) (val4 : aspis_core.field.QM31) (queries : Array U32 22#usize) (semantic_alpha : Array aspis_core.field.QM31 10#usize) (val6 : aspis_core.field.QM31) (val7 : aspis_core.field.QM31) (val8 : aspis_core.field.QM31) (val9 : aspis_core.field.QM31) (val10 : aspis_core.field.wide_exact.WideExact) (val11 : aspis_core.field.wide_exact.WideExact) (val12 : aspis_core.field.QM31) (r50 : verifier.Reader) :
 Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let i30 ←
   (fun v=>AspisR1.CheckpointBytes4Ops.finalLen (NIL_Carriers.variant v)) v
 let q ←
   (ok (NIL_Carriers.unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))
 let r51 ←
   (NIL_FreshOps.filled reserved)
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
     NIL_FreshOps.weights
       bytes r50.«at» val13
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
            variant := v,
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
              queries,
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

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (val2 : aspis_core.field.wide_exact.WideExact) (val3 : aspis_core.field.wide_exact.WideExact) (val4 : aspis_core.field.QM31) (queries : Array U32 22#usize) (semantic_alpha : Array aspis_core.field.QM31 10#usize) (val6 : aspis_core.field.QM31) (val7 : aspis_core.field.QM31) (val8 : aspis_core.field.QM31) (val9 : aspis_core.field.QM31) (val10 : aspis_core.field.wide_exact.WideExact) (val11 : aspis_core.field.wide_exact.WideExact) (r48 : verifier.Reader) :
 NIY_AfterRhs.suffix reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha val6 val7 val8 val9 val10 val11 r48=
 (do let (reply,out) ← NIL_FreshOps.readK r48
     NIL_TryTransport.fresh reply (fun x=>suffix reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha val6 val7 val8 val9 val10 val11 x out)) := by
 unfold NIY_AfterRhs.suffix
 apply NIL_ResultCases.bind_congr
 rintro ⟨reply,out⟩
 cases reply <;> rfl
#print axioms source
end NIY_AfterPower
