import AspisR1ActualSemanticRoundCutV1.Funs
import AspisR1PublicPreparation.Funs
import ActualSamplerGuardedBodyRefinementV1

set_option autoImplicit false
namespace AspisR1ActualSamplerDivPassTransportV1
open Aeneas Aeneas.Std Result ControlFlow

abbrev State := Array U32 8#usize × U64 × Usize
abbrev Output := Array U32 8#usize × U64

def actualBody (s : State) : Result (ControlFlow State Output) :=
  AspisR1ActualSemanticRoundCutV1.sampler.qm31_div_pass_loop.body
    s.1 s.2.1 s.2.2

def publicBody (s : State) : Result (ControlFlow State Output) :=
  AspisR1PublicPreparation.sampler.qm31_div_pass_loop.body
    s.1 s.2.1 s.2.2

theorem callback_eq : actualBody = publicBody := by
  funext s
  rcases s with ⟨rank,remainder,j⟩
  exact AspisR1ActualSamplerBodyRefinementV1.div_pass_body_eq rank remainder j

theorem loop_eq (rank : Array U32 8#usize) (remainder : U64) (j : Usize) :
    AspisR1ActualSemanticRoundCutV1.sampler.qm31_div_pass_loop rank remainder j =
    AspisR1PublicPreparation.sampler.qm31_div_pass_loop rank remainder j := by
  unfold AspisR1ActualSemanticRoundCutV1.sampler.qm31_div_pass_loop
    AspisR1PublicPreparation.sampler.qm31_div_pass_loop
  exact congrArg (fun body : State → Result (ControlFlow State Output) =>
    Aeneas.Std.loop body (rank,remainder,j)) callback_eq

#print axioms callback_eq
#print axioms loop_eq
end AspisR1ActualSamplerDivPassTransportV1
