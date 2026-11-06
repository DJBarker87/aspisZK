import NKM_CircleModel
import NKM_FallbackCertificate
set_option autoImplicit false
noncomputable section
namespace NKM_FallbackModel
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase AspisV8R19 R0P.SemSource
open NKM_circle NKM_FieldLaws NKM_CircleModel

def parameter0 : NKM_circle.field.QM31 := ⟨NKM_circle.field.CM31.ZERO,NKM_circle.field.CM31.ONE⟩
def parameter1 : NKM_circle.field.QM31 := ⟨NKM_circle.field.CM31.ONE,NKM_circle.field.CM31.ONE⟩

theorem parameter0_encode : parameter0 = encode circleFallbackParameter0 := by
 simp only [parameter0,NKM_circle.field.CM31.ZERO,NKM_circle.field.CM31.ONE,encode,fromQ,fromCM,
  SamplerClosureProductExecution.encode,SamplerClosureProductExecution.encodeCM,circleFallbackParameter0]
 rfl

theorem parameter1_encode : parameter1 = encode circleFallbackParameter1 := by
 simp only [parameter1,NKM_circle.field.CM31.ONE,encode,fromQ,fromCM,
  SamplerClosureProductExecution.encode,SamplerClosureProductExecution.encodeCM,circleFallbackParameter1]
 rfl

theorem parameter0_output : NKM_circle.circle.secure_ood_circle_point_from_parameter parameter0 =
 ok (.Ok (point circleFallbackParameter0)) := by
 rw [parameter0_encode,ood_total]
 simp only [oodResult,NKM_FallbackCertificate.denominator0,circleFallbackParameter0_im,if_false]

theorem parameter1_output : NKM_circle.circle.secure_ood_circle_point_from_parameter parameter1 =
 ok (.Ok (point circleFallbackParameter1)) := by
 rw [parameter1_encode,ood_total]
 simp only [oodResult,NKM_FallbackCertificate.denominator1,circleFallbackParameter1_im,if_false]

theorem array_index {α : Type} {n : Usize} (a : Array α n) (i : Usize) (hi : i.val < n.val) :
 Array.index_usize a i = ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
 have hidx : i.val < a.val.length := by simpa [a.property] using hi
 unfold Array.index_usize
 change (match a.val[i.val]? with | none => Result.fail Error.arrayOutOfBounds | some x => Result.ok x) = _
 rw [List.getElem?_eq_getElem hidx]

theorem entry0 : Array.index_usize NKM_circle.transcript.CIRCLE_FALLBACK_PARAMETERS 0#usize = ok parameter0 := by
 rw [array_index _ _ (by decide)]
 simp only [NKM_circle.transcript.CIRCLE_FALLBACK_PARAMETERS,Array.make,parameter0]
 rfl

theorem entry1 : Array.index_usize NKM_circle.transcript.CIRCLE_FALLBACK_PARAMETERS 1#usize = ok parameter1 := by
 rw [array_index _ _ (by decide)]
 simp only [NKM_circle.transcript.CIRCLE_FALLBACK_PARAMETERS,Array.make,parameter1]
 rfl

theorem fallback0 : NKM_circle.transcript.circle_fallback_point 0#usize = ok (point circleFallbackParameter0) := by
 unfold NKM_circle.transcript.circle_fallback_point
 rw [show (0#usize % 2#usize) = ok 0#usize by rfl]
 simp only [bind_tc_ok,entry0,parameter0_output]

theorem fallback1 : NKM_circle.transcript.circle_fallback_point 1#usize = ok (point circleFallbackParameter1) := by
 unfold NKM_circle.transcript.circle_fallback_point
 rw [show (1#usize % 2#usize) = ok 1#usize by rfl]
 simp only [bind_tc_ok,entry1,parameter1_output]

/-- The deployed caller constructs exactly this index from its two-case row enum. -/
def index (row : AspisR1CircleSampleWrapper.r0_transcript.CircleRow) : Usize :=
 match row with | .First => 0#usize | .Second => 1#usize

theorem caller_domain (row : AspisR1CircleSampleWrapper.r0_transcript.CircleRow) : index row = 0#usize ∨ index row = 1#usize := by
 cases row
 · exact Or.inl rfl
 · exact Or.inr rfl

theorem caller_result (row : AspisR1CircleSampleWrapper.r0_transcript.CircleRow) :
 NKM_circle.transcript.circle_fallback_point (index row) = ok
 (match row with | .First => point circleFallbackParameter0 | .Second => point circleFallbackParameter1) := by
 cases row
 · exact fallback0
 · exact fallback1

#print axioms parameter0_encode
#print axioms parameter1_encode
#print axioms parameter0_output
#print axioms parameter1_output
#print axioms array_index
#print axioms entry0
#print axioms entry1
#print axioms fallback0
#print axioms fallback1
#print axioms caller_domain
#print axioms caller_result
end NKM_FallbackModel
end
