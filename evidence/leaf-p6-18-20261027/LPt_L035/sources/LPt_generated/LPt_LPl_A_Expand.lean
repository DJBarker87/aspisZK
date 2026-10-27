import LPt_LPl_Kit_FunsExternal
import LPt_LPl_A_Map
open Aeneas Aeneas.Std Result
open LPt_LPl_Kit_Release
set_option autoImplicit false
namespace LPt_LPl_A.Expand
-- Native stage: compact::LPt_LPl_A_compact::LPt_LPl_A_expand_stage (K004), 29-stage index K006.
def byte (bs : List U8) (i : Nat) : U8 :=
  if i%32 < 16 then bs[i/32*16+i%32]?.getD 0#u8 else 0#u8
def loop (bs : List U8) (size : Nat) : List U8 := LPt_LPl_A.build (byte bs) size
theorem loop_eq_map (bs : List U8) (size : Nat) :
    loop bs size = (List.range size).map (byte bs) := LPt_LPl_A.build_map _ _
theorem loop_eq_fold (bs : List U8) (size : Nat) :
    loop bs size = (List.range size).foldl (fun xs i => xs ++ [byte bs i]) [] :=
  LPt_LPl_A.build_fold _ _
theorem shipped_leaf_model (bs out : Slice U8) :
    LPt_External.compact.expand_values bs out = (do
      if bs.val.length % 16 != 0 then ok (.Err .Length, out)
      else
        let size ← Slice.len bs * 2#usize
        if Slice.len out != size then ok (.Err .Length, out)
        else
          let values := loop bs.val out.val.length
          dite (values.length ≤ Usize.max)
            (fun h => ok (.Ok (), (⟨values,h⟩ : Slice U8)))
            (fun _ => fail .panic)) := by
  simp only [loop_eq_map]
  rfl
#print axioms loop_eq_map
#print axioms loop_eq_fold
#print axioms shipped_leaf_model
end LPt_LPl_A.Expand
