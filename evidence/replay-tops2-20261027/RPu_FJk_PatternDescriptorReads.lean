import RPu_FJk_CopyPatternDescriptor
import RPu_FJk_CarrierRead
set_option autoImplicit false
namespace AspisR1.FJk_PatternDescriptorReads
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FJk_CopyPatternDescriptor (model)
theorem kinds (p : CompiledPoolV1PairForestPattern) (i : Usize) (hi : i.val<16)
    (out : U8) (run : Array.index_usize p.kinds i=ok out) :
    (model p).kinds ⟨i.val,hi⟩=out.val := by
  exact congrArg UScalar.val (FJk_CarrierRead.value p.kinds i out hi run)
theorem offsets (p : CompiledPoolV1PairForestPattern) (i : Usize) (hi : i.val<16)
    (out : U32) (run : Array.index_usize p.offsets i=ok out) :
    (model p).offsets ⟨i.val,hi⟩=out.val := by
  exact congrArg UScalar.val (FJk_CarrierRead.value p.offsets i out hi run)
theorem columns (p : CompiledPoolV1PairForestPattern) (i : Usize) (hi : i.val<16)
    (out : U8) (ho : out.val<16) (run : Array.index_usize p.columns i=ok out) :
    (model p).columns ⟨i.val,hi⟩=⟨out.val,ho⟩ := by
  apply Fin.ext
  exact (congrArg (fun x : U8=>x.val%16) (FJk_CarrierRead.value p.columns i out hi run)).trans
    (Nat.mod_eq_of_lt ho)
#print axioms kinds
#print axioms offsets
#print axioms columns
end AspisR1.FJk_PatternDescriptorReads
