import NDH_Qm31Result
import LPk_Induction
set_option autoImplicit false
namespace NDH_Qm31NativeJoin
open Aeneas Aeneas.Std Result
open AspisR1.SamplerMachineBounds AspisR1.SamplerWordPass
open AspisR1.ExtractedQM31SamplerPassLoop

theorem decoded_lists_injective (xs ys : List U32)
    (equal : xs.map decode32 = ys.map decode32) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at equal
    | cons y ys =>
      have pair := List.cons.inj equal
      have values := congrArg UInt32.toNat pair.1
      have head : x=y := UScalar.eq_of_val_eq (by
        simpa only [decode32_val] using values)
      rw [head,ih ys pair.2]

theorem words_injective (xs ys : Array U32 8#usize)
    (equal : words xs = words ys) : xs=ys := by
  cases xs with | mk xs hx =>
    cases ys with | mk ys hy =>
      have values : xs=ys := decoded_lists_injective xs ys equal
      subst ys
      rfl

/-- A local native relation trace, not an assumed whole-function equality.
The writer contract fixes all old/new coordinates; LPk's native scalar gates
supply each div/rem relation. The last hypothesis is only the returned scalar
cast port, justified by remainder<P and the checked cast law. -/
theorem native_result (rank nativeOut : Array U32 8#usize)
    (nativeDigit : U32) (nativeRemainder : UInt64)
    (trace : LPk_Induction.Pass 0 (words rank).reverse
      nativeRemainder (words nativeOut).reverse)
    (return_cast : nativeDigit.val=nativeRemainder.toNat) :
    AspisR1Post25Sampler.sampler.qm31_div_pass rank = ok (nativeOut,nativeDigit) := by
  obtain ⟨out,digit,run,digitValue,outValue,_⟩ := NDH_Qm31Result.result rank
  have paired := LPk_Induction.pass_join trace (show (0:UInt64).toNat<P from P_pos)
  have wordsEqual := congrArg Prod.snd paired
  have digitEqual := congrArg (fun x : UInt64 × List UInt32 => x.1.toNat) paired
  have sameDigit : digit=nativeDigit := by
    apply UScalar.eq_of_val_eq
    rw [digitValue,return_cast,digitEqual]
  rw [←wordsEqual,List.reverse_reverse] at outValue
  have sameOut := words_injective out nativeOut outValue
  simpa only [sameOut,sameDigit] using run

#print axioms decoded_lists_injective
#print axioms words_injective
#print axioms native_result
end NDH_Qm31NativeJoin
