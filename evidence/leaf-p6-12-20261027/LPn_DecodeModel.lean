import LPn_Kit_DecodeModels
import LPl_A_Map
import LPl_A_FirstError
open Aeneas Aeneas.Std Result
open LPl_Kit_Release LPl_Kit_FieldExternal
set_option autoImplicit false
namespace LPn.DecodeModel
-- Native stage bridge: r1_wire::LPl_A_wire::LPl_A_decode_stage (K011).
def step (payload : List U8) (start i : Nat) : Bool × aspis_core.field.QM31 :=
  let bs := (payload.drop (start+32*i)).take 16
  let xs := (List.range 4).map fun j => LPn_Kit_word ((bs.drop (4*j)).take 4)
  (xs.all (fun x => x < 2147483647#u32), LPn_Kit_q xs)
def values (payload : List U8) (start n : Nat) := LPl_A.build (step payload start) n

theorem values_eq_map (payload : List U8) (start n : Nat) :
    values payload start n = (List.range n).map (step payload start) := LPl_A.build_map _ _

theorem values_eq_fold (payload : List U8) (start n : Nat) :
    values payload start n = (List.range n).foldl
      (fun xs i => xs ++ [step payload start i]) [] := LPl_A.build_fold _ _

theorem shipped_leaf_model (N : Usize) (r : r1_wire.ValidatedRecord) (offset : Usize) :
    r1_wire.ValidatedRecord.decode_k N r offset = (do
      if r.row < 14#u8 then ok (.Err .InvalidRow) else do
        let start := offset.val*32
        let size := N.val*32
        let finish := start+size
        if start > Usize.max ∨ size > Usize.max ∨ finish > Usize.max then ok (.Err (.Length r.row)) else do
          if r.framed.val.length < 5 then fail .panic else do
            let payload := r.framed.val.drop 5
            if finish > payload.length then ok (.Err (.Length r.row)) else do
              let vs := values payload start N.val
              match LPl_A.firstBad (fun i => !(vs[i]?.getD (true,qzero)).1) N.val with
              | some i =>
                dite (offset.val+i ≤ UScalar.cMax .Usize)
                  (fun h => ok (.Err (.NonCanonical r.row (UScalar.ofNat (offset.val+i) h))))
                  (fun _ => fail .panic)
              | none =>
                let xs := vs.map Prod.snd
                dite (xs.length = N.val) (fun h => ok (.Ok (⟨xs,h⟩ : Array aspis_core.field.QM31 N)))
                  (fun _ => fail .panic)) := by
  simp only [values_eq_map, LPl_A.firstBad_find]
  rfl
#print axioms values_eq_map
#print axioms values_eq_fold
#print axioms shipped_leaf_model
end LPn.DecodeModel
