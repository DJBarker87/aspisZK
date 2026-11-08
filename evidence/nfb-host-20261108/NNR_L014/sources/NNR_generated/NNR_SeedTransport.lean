import NNR_C04Domain
import NLT_Reseed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_SeedTransport
open Aeneas Aeneas.Std Result VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Merkle reply seeds may change; native occurrences still supply replies. -/
theorem source (wr rr : NP6_StdModel.Reservation) (left right : Merkle) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X) :
 NLT_Reseed.Same (NKE_CommonProgram.run wr rr left finish d pub proof ck hash none)
  (NKE_CommonProgram.run wr rr right finish d pub proof ck hash none) := by
 unfold NKE_CommonProgram.run
 repeat' first
 | (fail_if_no_progress dsimp only [Program.bind])
 | (apply NLT_Reseed.Same.call)
 | (apply NLT_Reseed.Same.prim)
 | (apply NLT_Reseed.Same.ret)
 | (intro value)
 | nlt_seed_eq
 | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
 | split
#print axioms source
end AspisR1.NNR_SeedTransport
end
