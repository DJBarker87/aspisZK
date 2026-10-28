import NDO_JGg_QueryDecode
set_option autoImplicit false
namespace AspisR1.JGg_QueryArrays
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JGg_Opening31.block0 JGg_Opening31.block1 JGg_Opening31.block2 JGg_Opening31.block3 JGg_Opening31.block4 JGg_Opening31.block5 JGg_Opening31.block6 JGg_Opening31.block7
attribute [local irreducible] JGg_Opening31.next0 JGg_Opening31.next1 JGg_Opening31.next2 JGg_Opening31.next3 JGg_Opening31.next4 JGg_Opening31.next5 JGg_Opening31.next6 JGg_Opening31.next7
def zero : Array U8 32#usize := Array.repeat 32#usize 0#u8
def initial : Array (Array U8 32#usize) 8#usize := Array.repeat 8#usize zero
def b1 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.block0,zero,zero,zero,zero,zero,zero,zero]
def b2 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.block0,encodeState JGg_Opening31.block1,zero,zero,zero,zero,zero,zero]
def b3 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.block0,encodeState JGg_Opening31.block1,encodeState JGg_Opening31.block2,zero,zero,zero,zero,zero]
def b4 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.block0,encodeState JGg_Opening31.block1,encodeState JGg_Opening31.block2,encodeState JGg_Opening31.block3,zero,zero,zero,zero]
def b5 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.block0,encodeState JGg_Opening31.block1,encodeState JGg_Opening31.block2,encodeState JGg_Opening31.block3,encodeState JGg_Opening31.block4,zero,zero,zero]
def b6 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.block0,encodeState JGg_Opening31.block1,encodeState JGg_Opening31.block2,encodeState JGg_Opening31.block3,encodeState JGg_Opening31.block4,encodeState JGg_Opening31.block5,zero,zero]
def b7 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.block0,encodeState JGg_Opening31.block1,encodeState JGg_Opening31.block2,encodeState JGg_Opening31.block3,encodeState JGg_Opening31.block4,encodeState JGg_Opening31.block5,encodeState JGg_Opening31.block6,zero]
def b8 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.block0,encodeState JGg_Opening31.block1,encodeState JGg_Opening31.block2,encodeState JGg_Opening31.block3,encodeState JGg_Opening31.block4,encodeState JGg_Opening31.block5,encodeState JGg_Opening31.block6,encodeState JGg_Opening31.block7]
def a1 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.next0,zero,zero,zero,zero,zero,zero,zero]
def a2 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.next0,encodeState JGg_Opening31.next1,zero,zero,zero,zero,zero,zero]
def a3 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.next0,encodeState JGg_Opening31.next1,encodeState JGg_Opening31.next2,zero,zero,zero,zero,zero]
def a4 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.next0,encodeState JGg_Opening31.next1,encodeState JGg_Opening31.next2,encodeState JGg_Opening31.next3,zero,zero,zero,zero]
def a5 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.next0,encodeState JGg_Opening31.next1,encodeState JGg_Opening31.next2,encodeState JGg_Opening31.next3,encodeState JGg_Opening31.next4,zero,zero,zero]
def a6 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.next0,encodeState JGg_Opening31.next1,encodeState JGg_Opening31.next2,encodeState JGg_Opening31.next3,encodeState JGg_Opening31.next4,encodeState JGg_Opening31.next5,zero,zero]
def a7 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.next0,encodeState JGg_Opening31.next1,encodeState JGg_Opening31.next2,encodeState JGg_Opening31.next3,encodeState JGg_Opening31.next4,encodeState JGg_Opening31.next5,encodeState JGg_Opening31.next6,zero]
def a8 : Array (Array U8 32#usize) 8#usize := Array.make 8#usize [encodeState JGg_Opening31.next0,encodeState JGg_Opening31.next1,encodeState JGg_Opening31.next2,encodeState JGg_Opening31.next3,encodeState JGg_Opening31.next4,encodeState JGg_Opening31.next5,encodeState JGg_Opening31.next6,encodeState JGg_Opening31.next7]
def back (x : Array U8 32#usize) : Array (Array U8 32#usize) 8#usize :=
  Array.make 8#usize [x,zero,zero,zero,zero,zero,zero,zero]
theorem mutable : Array.index_mut_usize initial 0#usize=ok (zero,back) := by rfl
#print axioms mutable
theorem back_b : back (encodeState JGg_Opening31.block0)=b1 := rfl
#print axioms back_b
theorem back_a : back (encodeState JGg_Opening31.next0)=a1 := rfl
#print axioms back_a
theorem b_update1 : Array.update b1 1#usize (encodeState JGg_Opening31.block1)=ok b2 := by rfl
#print axioms b_update1
theorem a_update1 : Array.update a1 1#usize (encodeState JGg_Opening31.next1)=ok a2 := by rfl
#print axioms a_update1
theorem b_update2 : Array.update b2 2#usize (encodeState JGg_Opening31.block2)=ok b3 := by rfl
#print axioms b_update2
theorem a_update2 : Array.update a2 2#usize (encodeState JGg_Opening31.next2)=ok a3 := by rfl
#print axioms a_update2
theorem b_update3 : Array.update b3 3#usize (encodeState JGg_Opening31.block3)=ok b4 := by rfl
#print axioms b_update3
theorem a_update3 : Array.update a3 3#usize (encodeState JGg_Opening31.next3)=ok a4 := by rfl
#print axioms a_update3
theorem b_update4 : Array.update b4 4#usize (encodeState JGg_Opening31.block4)=ok b5 := by rfl
#print axioms b_update4
theorem a_update4 : Array.update a4 4#usize (encodeState JGg_Opening31.next4)=ok a5 := by rfl
#print axioms a_update4
theorem b_update5 : Array.update b5 5#usize (encodeState JGg_Opening31.block5)=ok b6 := by rfl
#print axioms b_update5
theorem a_update5 : Array.update a5 5#usize (encodeState JGg_Opening31.next5)=ok a6 := by rfl
#print axioms a_update5
theorem b_update6 : Array.update b6 6#usize (encodeState JGg_Opening31.block6)=ok b7 := by rfl
#print axioms b_update6
theorem a_update6 : Array.update a6 6#usize (encodeState JGg_Opening31.next6)=ok a7 := by rfl
#print axioms a_update6
theorem b_update7 : Array.update b7 7#usize (encodeState JGg_Opening31.block7)=ok b8 := by rfl
#print axioms b_update7
theorem a_update7 : Array.update a7 7#usize (encodeState JGg_Opening31.next7)=ok a8 := by rfl
#print axioms a_update7
theorem state0 : Array.index_usize a1 0#usize=ok (encodeState JGg_Opening31.next0) := by rfl
#print axioms state0
theorem state1 : Array.index_usize a2 1#usize=ok (encodeState JGg_Opening31.next1) := by rfl
#print axioms state1
theorem state2 : Array.index_usize a3 2#usize=ok (encodeState JGg_Opening31.next2) := by rfl
#print axioms state2
theorem state3 : Array.index_usize a4 3#usize=ok (encodeState JGg_Opening31.next3) := by rfl
#print axioms state3
theorem state4 : Array.index_usize a5 4#usize=ok (encodeState JGg_Opening31.next4) := by rfl
#print axioms state4
theorem state5 : Array.index_usize a6 5#usize=ok (encodeState JGg_Opening31.next5) := by rfl
#print axioms state5
theorem state6 : Array.index_usize a7 6#usize=ok (encodeState JGg_Opening31.next6) := by rfl
#print axioms state6
theorem state7 : Array.index_usize a8 7#usize=ok (encodeState JGg_Opening31.next7) := by rfl
#print axioms state7
theorem blocks : b8=JGg_QueryDecode.blocks := rfl
#print axioms blocks
theorem advances : a8=JGg_QueryDecode.advances := rfl
#print axioms advances
end AspisR1.JGg_QueryArrays
