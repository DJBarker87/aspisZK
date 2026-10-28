import NCV_ArrayRun
import NCV_ArrayRead
set_option autoImplicit false
namespace AspisR1.JHu_ReferenceBytes
open Aeneas Aeneas.Std Result

/-- A byte read is transported through one bounded field, never through buffer reduction. -/
theorem field_byte (b : Slice U8) (s : Usize) (a : Array U8 32#usize)
    (fit : s.val+32 ≤ b.val.length)
    (field : (b.val.drop s.val).take 32=a.val) (j : Nat) (hj : j<32) :
    NCV_ZeroStep.byte b (s.val+j)=NCV_ArrayFrame.coord a j := by
  have h:=congrArg (fun xs : List U8 => xs[j]?.getD 0#u8) field
  have ha : j<a.val.length := by rw [a.property];exact hj
  simpa only [List.getElem?_eq_getElem ha,Option.getD_some,List.getElem?_take,if_pos hj,List.getElem?_drop,NCV_ZeroStep.byte,
    NCV_ArrayFrame.coord] using h
#print axioms field_byte

/-- Complete E008 byte-copy loop, by the generic array frame induction. -/
theorem bytes32 (b : Slice U8) (s : Usize) (a : Array U8 32#usize)
    (cap : b.val.length ≤ 768) (fit : s.val+32 ≤ b.val.length)
    (field : (b.val.drop s.val).take 32=a.val) :
    NCV_Reference.bytes32 b s=ok a := by
  have steps : ∀ current i, i.val<(32#usize).val → ∃ next : Usize, next.val=i.val+1 ∧
      NCV_Reference.bytes32_loop.body b s current i=
        ok (.cont (current.set i (NCV_ArrayFrame.coord a i.val),next)) := by
    intro current i hi
    obtain ⟨next,nv,step⟩:=NCV_ByteStep.step b s i current cap fit hi
    exact ⟨next,nv,by simpa only [field_byte b s a fit field i.val hi] using step⟩
  unfold NCV_Reference.bytes32 NCV_Reference.bytes32_loop
  exact NCV_ArrayRun.run (fun (current,i)=>NCV_Reference.bytes32_loop.body b s current i)
    a id steps (fun current i h=>NCV_ByteStep.terminal b s i current h)
    _ 0#usize (by scalar_tac) (by intro j h; have hz : (0#usize).val=0 := rfl; rw [hz] at h; omega)
#print axioms bytes32
end AspisR1.JHu_ReferenceBytes
