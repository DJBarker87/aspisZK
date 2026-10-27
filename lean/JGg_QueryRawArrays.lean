import JGg_QueryArrays
set_option autoImplicit false
namespace AspisR1.JGg_QueryRawArrays
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge
def b1 : Array (Array U8 32#usize) 8#usize := JGg_QueryArrays.initial.set 0#usize (encodeState JGg_Opening31.block0)
def b2 : Array (Array U8 32#usize) 8#usize :=
  ⟨b1.val.set 1 (encodeState JGg_Opening31.block1),by simpa only [List.length_set] using b1.property⟩
def b3 : Array (Array U8 32#usize) 8#usize :=
  ⟨b2.val.set 2 (encodeState JGg_Opening31.block2),by simpa only [List.length_set] using b2.property⟩
def b4 : Array (Array U8 32#usize) 8#usize :=
  ⟨b3.val.set 3 (encodeState JGg_Opening31.block3),by simpa only [List.length_set] using b3.property⟩
def b5 : Array (Array U8 32#usize) 8#usize :=
  ⟨b4.val.set 4 (encodeState JGg_Opening31.block4),by simpa only [List.length_set] using b4.property⟩
def b6 : Array (Array U8 32#usize) 8#usize :=
  ⟨b5.val.set 5 (encodeState JGg_Opening31.block5),by simpa only [List.length_set] using b5.property⟩
def b7 : Array (Array U8 32#usize) 8#usize :=
  ⟨b6.val.set 6 (encodeState JGg_Opening31.block6),by simpa only [List.length_set] using b6.property⟩
def b8 : Array (Array U8 32#usize) 8#usize :=
  ⟨b7.val.set 7 (encodeState JGg_Opening31.block7),by simpa only [List.length_set] using b7.property⟩
theorem b_same : b8=JGg_QueryArrays.b8 := by apply Subtype.ext;rfl
#print axioms b_same
def a1 : Array (Array U8 32#usize) 8#usize := JGg_QueryArrays.initial.set 0#usize (encodeState JGg_Opening31.next0)
def a2 : Array (Array U8 32#usize) 8#usize :=
  ⟨a1.val.set 1 (encodeState JGg_Opening31.next1),by simpa only [List.length_set] using a1.property⟩
def a3 : Array (Array U8 32#usize) 8#usize :=
  ⟨a2.val.set 2 (encodeState JGg_Opening31.next2),by simpa only [List.length_set] using a2.property⟩
def a4 : Array (Array U8 32#usize) 8#usize :=
  ⟨a3.val.set 3 (encodeState JGg_Opening31.next3),by simpa only [List.length_set] using a3.property⟩
def a5 : Array (Array U8 32#usize) 8#usize :=
  ⟨a4.val.set 4 (encodeState JGg_Opening31.next4),by simpa only [List.length_set] using a4.property⟩
def a6 : Array (Array U8 32#usize) 8#usize :=
  ⟨a5.val.set 5 (encodeState JGg_Opening31.next5),by simpa only [List.length_set] using a5.property⟩
def a7 : Array (Array U8 32#usize) 8#usize :=
  ⟨a6.val.set 6 (encodeState JGg_Opening31.next6),by simpa only [List.length_set] using a6.property⟩
def a8 : Array (Array U8 32#usize) 8#usize :=
  ⟨a7.val.set 7 (encodeState JGg_Opening31.next7),by simpa only [List.length_set] using a7.property⟩
theorem a_same : a8=JGg_QueryArrays.a8 := by apply Subtype.ext;rfl
#print axioms a_same
end AspisR1.JGg_QueryRawArrays
