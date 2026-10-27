import LPn_ClaimsPrefix
open Aeneas Aeneas.Std Result LPl_Kit_Release LPl_Kit_FieldExternal
set_option autoImplicit false
namespace LPn.Claims
open LPn.ClaimsModel

theorem decode_total (N : Usize) (r : r1_wire.ValidatedRecord) (off : Usize)
    (ready : LPn.Decode.Ready N r off) (bound : r.framed.val.length≤3717) :
    ∃ out, r1_wire.ValidatedRecord.decode_k N r off = ok out := by
  obtain ⟨out,scan⟩ := LPl.Scan.exists_trace
    (LPn.Decode.predicate (r.framed.val.drop 5) (off.val*32) N.val) N.val 0 N.val (by omega) (by omega)
  cases out with
  | some i =>
    have safe := (LPn.Decode.error_bound N r off ready bound i scan).2
    exact ⟨.Err (.NonCanonical r.row (UScalar.ofNat (off.val+i) safe)),
      LPn.Decode.native_error N r off ready i scan safe⟩
  | none =>
    let initial := List.replicate N.val qzero
    obtain ⟨after,writes⟩ := LPn.Decode.total (r.framed.val.drop 5) (off.val*32) initial N.val
    have ilen : initial.length=N.val := List.length_replicate
    have size : after.length=N.val := (LPn.Decode.length _ _ initial after N.val writes).trans ilen
    let a : Array LPn.Decode.Q N := ⟨after,size⟩
    exact ⟨.Ok a,LPn.Decode.native_success N r off initial a ready ilen scan writes⟩

theorem offset_value (point : Nat) (hp : point<3) :
    (LPn_Kit_usize (point*29)).val=point*29 := by
  change (point*29) % (UScalar.cMax .Usize+1) = point*29
  apply Nat.mod_eq_of_lt
  have small : point*29≤58 := by omega
  scalar_tac

theorem point_ready (p : r1_wire.Prefix) (point : Nat) (hp : point<3)
    (shape : (framed p).val.length=3717) :
    LPn.Decode.Ready 29#usize (record p) (LPn_Kit_usize (point*29)) := by
  have off := offset_value point hp
  have small : point*29≤58 := by omega
  constructor
  · change ¬ (25#u8)<14#u8;scalar_tac
  · change ¬ ((LPn_Kit_usize (point*29)).val*32>Usize.max ∨
      (29#usize).val*32>Usize.max ∨ (LPn_Kit_usize (point*29)).val*32+(29#usize).val*32>Usize.max)
    rw [off];scalar_tac
  · change ¬ (framed p).val.length<5;omega
  · change ¬ (LPn_Kit_usize (point*29)).val*32+(29#usize).val*32>((framed p).val.drop 5).length
    rw [off,List.length_drop,shape]
    norm_num only [UScalar.ofNatCore_val_eq]
    omega

theorem total (p : r1_wire.Prefix) (n : Nat) (hp : n≤3)
    (shape : (framed p).val.length=3717) :
    ∃ after, Trace (record p) n after := by
  induction n with
  | zero => exact ⟨.Ok [],.init⟩
  | succ n ih =>
    obtain ⟨before,rest⟩ := ih (by omega)
    cases before with
    | Err e => exact ⟨.Err e,.next n _ _ rest (.stopped e n)⟩
    | Ok rows =>
      obtain ⟨out,call⟩ := decode_total 29#usize (record p) (LPn_Kit_usize (n*29))
        (point_ready p n (by omega) shape) (by exact Nat.le_of_eq shape)
      cases out with
      | Err e => exact ⟨.Err e,.next n _ _ rest (.reject rows n e call)⟩
      | Ok row => exact ⟨.Ok (rows++[row]),.next n _ _ rest (.write rows n row call)⟩

#print axioms decode_total
#print axioms offset_value
#print axioms point_ready
#print axioms total
end LPn.Claims
