import PV_LIB_A_F124LocalResolver15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F124CallResolvers15
open PV_STX2_Syntax
open PV_LIB_A_Full124TableGap14 PV_LIB_A_F124LocalResolver15

def calls : List Data :=
  [PV_THR2_Packet124Children.fn7, PV_THR2_Packet124Children.fn9,
   PV_THR2_Packet124BoxIssue17.fn, PV_THR2_PacketEnter216.fn,
   PV_THR2_Packet124ReturnData.intoFn, PV_THR2_Packet124ReturnData.arcFn,
   PV_THR2_Packet218ReturnData.fn, PV_THR2_Packet216Children.fn5,
   PV_THR2_Packet216Children.fn15]

/-- At the exact emitted CLOSED124 call descriptors, the complete provider
resolver and Full-compatible table agree. Unlike a whole-table equality,
this checks only calls in124 and its CLOSED216/218/315 descendants. No body
is unfolded, and no execution/native-success fact is assumed. -/
theorem actual (bodies : Nat → Option PV_STX2_SliceSyntax.Program)
    (traits : Data → Option PV_STX2_SliceSyntax.Program) (h : Bindings bodies)
    (box : traits PV_THR2_Packet124BoxIssue17.fn = none)
    (d : Data) (member : d ∈ calls) :
    PV_THR2_PacketConstructorLocalTable.table
      (PV_THR2_PacketOriginalTable.table (fullRegular bodies traits)) d =
      fullRegular bodies traits d := by
  simp only [calls, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change none = bodies 121; exact h.native121.symm
  · change none = bodies 121; exact h.native121.symm
  · rw [PV_THR2_PacketConstructorLocalTable.atBox]
    change none = traits PV_THR2_Packet124BoxIssue17.fn
    exact box.symm
  · change some PV_THR2_F216.live = bodies 216; exact h.body216.symm
  · change none = bodies 217; exact h.native217.symm
  · change some PV_THR2_F218.live = bodies 218; exact h.body218.symm
  · change some PV_THR2_F315.live = bodies 315; exact h.body315.symm
  · change none = bodies 312; exact h.native312.symm
  · change none = bodies 313; exact h.native313.symm

#print axioms calls
#print axioms actual
end PV_LIB_A_F124CallResolvers15
