import RPu_FIp_FinalSumStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_FinalSum
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
open FIp_FinalSumStep

theorem loop_value (parts k : Array NE 7#usize) (hp : FIo_ArrayCanon.Holds parts) (hk : FIo_ArrayCanon.Holds k)
    (iter : FIo_RangeNext.Range) (sum result : NE)
    (stop : Nat) (initial : AspisWideTower.WideExact) (inv : Inv parts k stop initial (iter,sum))
    (run : FIo_Native.weights.Weights.pair_loop17 iter parts k sum=ok result) :
    Post parts k stop initial result := by
  exact FIo_LoopInvariant.preserve
    (fun s : State => FIo_Native.weights.Weights.pair_loop17.body parts k s.1 s.2)
    (Inv parts k stop initial) (Post parts k stop initial) measure
    (fun s h out hr => by cases out <;> exact step parts k hp hk stop initial s h _ hr)
    (iter,sum) result inv run

theorem seven (parts k : Array NE 7#usize) (hp : FIo_ArrayCanon.Holds parts) (hk : FIo_ArrayCanon.Holds k)
    (out : NE)
    (run : FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
      FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out) :
    FIo_WideValues.Canon out ∧ decodeWide (wide out)=FIp_Prefix.sumPrefix parts k 7 := by
  have h := loop_value parts k hp hk _ _ out 7 0
    ⟨FIo_Constants.zero.1,rfl,by decide,by change decodeWide (wide FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=0+FIp_Prefix.sumPrefix parts k 0; rw [FIo_Constants.zero.2,FIp_Prefix.zero,add_zero]⟩ run
  exact ⟨h.1,by simpa only [zero_add] using h.2⟩

#print axioms loop_value
#print axioms seven
end AspisR1.FIp_FinalSum
end
