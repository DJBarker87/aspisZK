import CPH_Program
import S2W_ReturnedCheckpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_RecordedKeys
open Aeneas Aeneas.Std
/-- Exact physical keys in the retained accepted default-ELF pair: proof,
physical public, CP, then the five additional TX2 accounts. No key files are read. -/
def key : Nat → S2W_ExtractionBoundary.Program
  | 0 => Array.make 32#usize [69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8, 69#u8]
  | 1 => Array.make 32#usize [70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8, 70#u8]
  | 2 => Array.make 32#usize [64#u8, 31#u8, 124#u8, 157#u8, 95#u8, 143#u8, 134#u8, 234#u8, 28#u8, 196#u8, 24#u8, 89#u8, 169#u8, 140#u8, 24#u8, 26#u8, 130#u8, 199#u8, 248#u8, 161#u8, 64#u8, 224#u8, 174#u8, 52#u8, 43#u8, 226#u8, 180#u8, 93#u8, 235#u8, 38#u8, 251#u8, 245#u8]
  | 3 => Array.make 32#usize [34#u8, 8#u8, 198#u8, 55#u8, 61#u8, 211#u8, 19#u8, 178#u8, 242#u8, 118#u8, 165#u8, 45#u8, 20#u8, 254#u8, 147#u8, 25#u8, 55#u8, 157#u8, 211#u8, 124#u8, 152#u8, 170#u8, 59#u8, 88#u8, 182#u8, 77#u8, 252#u8, 152#u8, 45#u8, 26#u8, 82#u8, 63#u8]
  | 4 => Array.make 32#usize [196#u8, 102#u8, 84#u8, 170#u8, 104#u8, 43#u8, 219#u8, 48#u8, 186#u8, 107#u8, 137#u8, 83#u8, 94#u8, 246#u8, 77#u8, 0#u8, 95#u8, 194#u8, 23#u8, 211#u8, 45#u8, 133#u8, 134#u8, 108#u8, 194#u8, 76#u8, 167#u8, 72#u8, 207#u8, 114#u8, 192#u8, 205#u8]
  | 5 => Array.make 32#usize [32#u8, 73#u8, 231#u8, 207#u8, 1#u8, 77#u8, 136#u8, 117#u8, 47#u8, 206#u8, 98#u8, 125#u8, 13#u8, 237#u8, 112#u8, 176#u8, 187#u8, 122#u8, 65#u8, 248#u8, 189#u8, 141#u8, 180#u8, 25#u8, 45#u8, 142#u8, 52#u8, 8#u8, 202#u8, 78#u8, 16#u8, 28#u8]
  | 6 => Array.make 32#usize [255#u8, 103#u8, 20#u8, 29#u8, 19#u8, 195#u8, 72#u8, 121#u8, 184#u8, 207#u8, 93#u8, 169#u8, 153#u8, 36#u8, 142#u8, 171#u8, 200#u8, 92#u8, 79#u8, 107#u8, 186#u8, 169#u8, 198#u8, 210#u8, 115#u8, 193#u8, 229#u8, 236#u8, 239#u8, 214#u8, 81#u8, 30#u8]
  | _ => Array.make 32#usize [17#u8, 154#u8, 124#u8, 153#u8, 113#u8, 147#u8, 61#u8, 254#u8, 52#u8, 68#u8, 8#u8, 149#u8, 99#u8, 67#u8, 208#u8, 166#u8, 22#u8, 170#u8, 233#u8, 162#u8, 174#u8, 18#u8, 23#u8, 198#u8, 192#u8, 115#u8, 178#u8, 38#u8, 251#u8, 80#u8, 120#u8, 152#u8]

theorem native_injective (i j : Nat) (hi : i < 8) (hj : j < 8)
    (same : (key i).val.map S2W_ReturnedCheckpoint.nativeByte =
      (key j).val.map S2W_ReturnedCheckpoint.nativeByte) : i = j := by
  have head := congrArg (fun xs : List UInt8 => xs[0]?) same
  interval_cases i <;> interval_cases j <;>
    first | rfl | exact False.elim ((of_decide_eq_false (by rfl)) head)

theorem injective (i j : Nat) (hi : i < 8) (hj : j < 8) (same : key i = key j) : i = j :=
  native_injective i j hi hj (congrArg (fun k : S2W_ExtractionBoundary.Program =>
    k.val.map S2W_ReturnedCheckpoint.nativeByte) same)

#print axioms native_injective
#print axioms injective
end AspisR1.CPH_RecordedKeys
end
