import NIY_AllocationCut
import NIL_AllocationPort
set_option autoImplicit false
noncomputable section
namespace NIY_FinalCut
open Aeneas Aeneas.Std Result ControlFlow Error NID_ResumeEmission

def finish (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (val2 : aspis_core.field.wide_exact.WideExact) (val3 : aspis_core.field.wide_exact.WideExact) (val4 : aspis_core.field.QM31) (queries : Array U32 22#usize) (semantic_alpha : Array aspis_core.field.QM31 10#usize) (val6 : aspis_core.field.QM31) (val7 : aspis_core.field.QM31) (val8 : aspis_core.field.QM31) (val9 : aspis_core.field.QM31) (val10 : aspis_core.field.wide_exact.WideExact) (val11 : aspis_core.field.wide_exact.WideExact) (val12 : aspis_core.field.QM31) (weights : alloc.vec.Vec aspis_core.field.QM31) (at2 : Usize) (r50 : verifier.Reader) :
 Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
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

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (val2 : aspis_core.field.wide_exact.WideExact) (val3 : aspis_core.field.wide_exact.WideExact) (val4 : aspis_core.field.QM31) (queries : Array U32 22#usize) (semantic_alpha : Array aspis_core.field.QM31 10#usize) (val6 : aspis_core.field.QM31) (val7 : aspis_core.field.QM31) (val8 : aspis_core.field.QM31) (val9 : aspis_core.field.QM31) (val10 : aspis_core.field.wide_exact.WideExact) (val11 : aspis_core.field.wide_exact.WideExact) (val12 : aspis_core.field.QM31) (val13 : alloc.vec.Vec aspis_core.field.QM31) (r50 : verifier.Reader) :
 NIY_AllocationCut.suffix reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha val6 val7 val8 val9 val10 val11 val12 val13 r50=
 (do let reply ← NIL_FreshOps.weights bytes r50.«at» val13
     NIL_TryTransport.fresh reply (fun (weights,at2)=>finish reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha val6 val7 val8 val9 val10 val11 val12 weights at2 r50)) := by
 unfold NIY_AllocationCut.suffix
 apply NIL_ResultCases.bind_congr
 intro reply
 cases reply with
 | Ok pair => rcases pair with ⟨weights,at2⟩;rfl
 | Err err => rfl
#print axioms source
end NIY_FinalCut
