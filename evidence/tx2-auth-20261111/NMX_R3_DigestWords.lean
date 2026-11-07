import NMX_R3_PrimaryWindow
import NMX_R3_WordRead
set_option autoImplicit false
namespace NMX_R3_DigestWords
open Aeneas Aeneas.Std Result

def limb (b : Slice U8) (s k : Nat) : U32 :=
 core.num.U32.from_le_bytes (NDB_PrimaryWords.window b (s+4*k) 4#usize)
def target (b : Slice U8) (s : Nat) : Array U32 8#usize :=
 ⟨List.ofFn (fun i : Fin 8 => limb b s i.val), by simp⟩

theorem coordinate (b : Slice U8) (s k : Nat) (index : k < 8) :
 NCV_ArrayFrame.coord (target b s) k = limb b s k := by
 simp only [NCV_ArrayFrame.coord, target,
  List.getElem?_eq_getElem (show k < (List.ofFn (fun i : Fin 8 => limb b s i.val)).length by simpa using index),
  List.getElem_ofFn, Option.getD_some]

theorem read (b : Slice U8) (s : Usize) (k : Nat) (index : k < 8)
 (fit : s.val + 32 ≤ b.val.length) (addr : Usize) (same : addr.val = s.val + 4*k) :
 NCV_Reference.word32 b addr = ok (limb b s.val k) := by
 rw [NDB_PrimaryWords.word32 b addr (by omega)]
 simp only [limb, same]
#print axioms coordinate
#print axioms read
end NMX_R3_DigestWords
