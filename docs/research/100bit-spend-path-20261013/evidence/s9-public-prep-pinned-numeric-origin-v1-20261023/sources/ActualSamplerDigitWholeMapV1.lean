import AspisR1ActualSemanticRoundCutV1.Funs
import AspisR1PublicPreparation.Funs
import ActualSamplerDigitLoopTransportV1
import ActualSamplerDivPassTransportV1

set_option autoImplicit false
namespace AspisR1ActualSamplerDigitWholeMapV1
open Aeneas Aeneas.Std Result ControlFlow

abbrev State0 := (Array U32 8#usize) × Usize
abbrev State1 := (Array U32 8#usize) × (Array U32 4#usize) × Usize
abbrev Result0 := Result (ControlFlow State0 (Array U32 8#usize))
abbrev Result1 := Result (ControlFlow State1 (Array U32 4#usize))

def toPublicQM
    (q : AspisR1ActualSemanticRoundCutV1.aspis_core.field.QM31) :
    AspisR1PublicPreparation.aspis_core.field.QM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def actualBody0 (block : Array U8 32#usize) (s : State0) : Result0 :=
  AspisR1ActualSemanticRoundCutV1.sampler.qm31_digits_loop0.body block s.1 s.2

def publicBody0 (block : Array U8 32#usize) (s : State0) : Result0 :=
  AspisR1PublicPreparation.sampler.qm31_digits_loop0.body block s.1 s.2

def actualBody1 (s : State1) : Result1 :=
  AspisR1ActualSemanticRoundCutV1.sampler.qm31_digits_loop1.body s.1 s.2.1 s.2.2

def publicBody1 (s : State1) : Result1 :=
  AspisR1PublicPreparation.sampler.qm31_digits_loop1.body s.1 s.2.1 s.2.2

theorem callback0_eq (block : Array U8 32#usize) : actualBody0 block = publicBody0 block := by
  funext s
  rcases s with ⟨rank,i⟩
  exact AspisR1ActualSamplerDigitLoopTransportV1.digits_loop0_body_eq block rank i

theorem loop0_eq (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize) :
    AspisR1ActualSemanticRoundCutV1.sampler.qm31_digits_loop0 block rank i =
      AspisR1PublicPreparation.sampler.qm31_digits_loop0 block rank i := by
  unfold AspisR1ActualSemanticRoundCutV1.sampler.qm31_digits_loop0
    AspisR1PublicPreparation.sampler.qm31_digits_loop0
  change Aeneas.Std.loop (actualBody0 block) (rank,i) =
    Aeneas.Std.loop (publicBody0 block) (rank,i)
  exact congrArg (fun b : State0 → Result0 => Aeneas.Std.loop b (rank,i))
    (callback0_eq block)

theorem callback1_eq : actualBody1 = publicBody1 := by
  funext s
  rcases s with ⟨rank,digits,i⟩
  exact AspisR1ActualSamplerDigitLoopTransportV1.digits_loop1_body_eq rank digits i

theorem loop1_eq (rank : Array U32 8#usize) (digits : Array U32 4#usize) (i : Usize) :
    AspisR1ActualSemanticRoundCutV1.sampler.qm31_digits_loop1 rank digits i =
      AspisR1PublicPreparation.sampler.qm31_digits_loop1 rank digits i := by
  unfold AspisR1ActualSemanticRoundCutV1.sampler.qm31_digits_loop1
    AspisR1PublicPreparation.sampler.qm31_digits_loop1
  change Aeneas.Std.loop actualBody1 (rank,digits,i) =
    Aeneas.Std.loop publicBody1 (rank,digits,i)
  exact congrArg (fun b : State1 → Result1 => Aeneas.Std.loop b (rank,digits,i))
    callback1_eq

theorem digits_result_eq (block : Array U8 32#usize) :
    AspisR1ActualSemanticRoundCutV1.sampler.qm31_digits block =
      AspisR1PublicPreparation.sampler.qm31_digits block := by
  unfold AspisR1ActualSemanticRoundCutV1.sampler.qm31_digits
    AspisR1PublicPreparation.sampler.qm31_digits
  dsimp only
  simp only [loop0_eq, loop1_eq]

theorem sample_result_map (block : Array U8 32#usize) :
    (do let q ← AspisR1ActualSemanticRoundCutV1.sampler.qm31_sample block
        ok (toPublicQM q)) =
      AspisR1PublicPreparation.sampler.qm31_sample block := by
  unfold AspisR1ActualSemanticRoundCutV1.sampler.qm31_sample
    AspisR1PublicPreparation.sampler.qm31_sample
  simp only [digits_result_eq,
    AspisR1ActualSemanticRoundCutV1.aspis_core.field.CM31.new,
    AspisR1PublicPreparation.aspis_core.field.CM31.new,
    bind_tc_ok, bind_assoc, toPublicQM]

#print axioms callback0_eq
#print axioms loop0_eq
#print axioms callback1_eq
#print axioms loop1_eq
#print axioms digits_result_eq
#print axioms sample_result_map
end AspisR1ActualSamplerDigitWholeMapV1
