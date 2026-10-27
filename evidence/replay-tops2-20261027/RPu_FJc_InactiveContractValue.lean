import RPu_FJc_InactiveContract
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_InactiveContractValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
open FJc_InactiveContract

theorem loop (low : Array NE 16#usize) (cs : Array NE 12#usize)
    (hlow : FIo_ArrayCanon.Holds low) (hcs : FIo_ArrayCanon.Holds cs)
    (stop : Nat) (initial : AspisWideTower.WideExact) (iter : FIo_RangeNext.Range) (w out : NE)
    (inv : Inv low cs stop initial (iter,w))
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1 iter low cs w=ok out) :
    Post low cs stop initial out := by
  exact FIo_LoopInvariant.preserve
    (fun s : State=>FIo_Native.weights.s2_grouped_inactive_pair_loop1.body low cs s.1 s.2)
    (Inv low cs stop initial) (Post low cs stop initial) FIo_GroupSubset.measure
    (fun s h r hr=>by cases r <;> exact step low cs hlow hcs stop initial s h _ hr)
    (iter,w) out inv run

theorem twelve (low : Array NE 16#usize) (cs : Array NE 12#usize)
    (hlow : FIo_ArrayCanon.Holds low) (hcs : FIo_ArrayCanon.Holds cs) (out : NE)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1
      {start:=0#usize,«end»:=12#usize} low cs
      FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out) :
    FIo_WideValues.Canon out ∧ decodeWide (wide out)=sumPrefix low cs 12 := by
  have v := loop low cs hlow hcs 12 0 _ _ out
    ⟨FIo_Constants.zero.1,rfl,by decide,by
      change decodeWide (wide FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=0+0
      rw [FIo_Constants.zero.2,add_zero]⟩ run
  exact ⟨v.1,by simpa only [zero_add] using v.2⟩
#print axioms loop
#print axioms twelve
end AspisR1.FJc_InactiveContractValue
end
