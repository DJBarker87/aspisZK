import FJc_SubsetStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_SubsetValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
open FJc_SubsetStep

theorem loop (low : Array NE 16#usize) (group : Usize) (hlow : FIo_ArrayCanon.Holds low)
    (stop : Nat) (initial : AspisWideTower.WideExact) (iter : FIo_RangeNext.Range) (w out : NE)
    (inv : Inv low group.val stop initial (iter,w))
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0 iter low group w=ok out) :
    Post low group.val stop initial out := by
  exact FIo_LoopInvariant.preserve
    (fun s : State=>FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body low group s.1 s.2)
    (Inv low group.val stop initial) (Post low group.val stop initial) FIo_GroupSubset.measure
    (fun s h r hr=>by cases r <;> exact step low group hlow stop initial s h _ hr)
    (iter,w) out inv run

theorem sixteen (low : Array NE 16#usize) (group : Usize) (hlow : FIo_ArrayCanon.Holds low) (out : NE)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0
      {start:=0#usize,«end»:=16#usize} low group
      FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out) :
    FIo_WideValues.Canon out ∧ decodeWide (wide out)=FJc_SubsetModel.sumPrefix low group.val 16 := by
  have v := loop low group hlow 16 0 _ _ out
    ⟨FIo_Constants.zero.1,rfl,by decide,by decide,by
      change decodeWide (wide FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=0+0
      rw [FIo_Constants.zero.2,add_zero]⟩ run
  exact ⟨v.1,by simpa only [zero_add] using v.2⟩
#print axioms loop
#print axioms sixteen
end AspisR1.FJc_SubsetValue
end
