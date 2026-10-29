import R1Z.PV_RunJoin_ClaimProducer48
import R1Z.PV_RunJoin_ByteAppend38
import R1Z.PV_RunJoin_WeightResult46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimImage48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ClaimThread48 (Column W)
open PV_RunJoin_WeightMap46 (mapResult)

def values (evaluate : Column → Result W) : List Column → Result (List W)
  | [] => ok []
  | c::cs => do let v ← evaluate c; let vs ← values evaluate cs; ok (v::vs)

def bytes : List W → List U8
  | [] => []
  | v::vs => (PV_RunJoin_FlatBytes35.wire v).val ++ bytes vs

theorem length (vs : List W) : (bytes vs).length=32*vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have wl : (PV_RunJoin_FlatBytes35.wire v).val.length=32 := (PV_RunJoin_FlatBytes35.wire v).property
    rw [bytes,List.length_append,wl,ih,List.length_cons]
    omega

theorem complete (evaluate : Column → Result W) (columns : List Column)
    (out : alloc.vec.Vec U8) (room : out.length+32*columns.length≤Usize.max) :
    mapResult (fun next => next.val) (PV_RunJoin_ClaimProducer48.run evaluate columns out)=
      mapResult (fun vs => out.val ++ bytes vs) (values evaluate columns) := by
  induction columns generalizing out with
  | nil => simp only [PV_RunJoin_ClaimProducer48.run,values,bytes,mapResult,PV_B2_E_OrdinaryOriginal.mapResult,List.append_nil]
  | cons c cs ih =>
    cases he : evaluate c with
    | fail e => simp only [PV_RunJoin_ClaimProducer48.run,values,he,bind_tc_fail,mapResult]
    | div => simp only [PV_RunJoin_ClaimProducer48.run,values,he,bind_tc_div,mapResult]
    | ok v =>
      obtain ⟨mid,hm,hv⟩ := PV_RunJoin_ByteAppend38.append out
        (Array.to_slice (PV_RunJoin_FlatBytes35.wire v)) (by
          change out.length+32≤Usize.max
          simp only [List.length_cons] at room
          omega)
      change mid.val=out.val ++ (PV_RunJoin_FlatBytes35.wire v).val at hv
      have wl : (PV_RunJoin_FlatBytes35.wire v).val.length=32 := (PV_RunJoin_FlatBytes35.wire v).property
      have ml : mid.length=out.length+32 := by
        change mid.val.length=out.val.length+32
        rw [hv,List.length_append,wl]
      simp only [PV_RunJoin_ClaimProducer48.run,values,he,bind_tc_ok,hm]
      rw [ih mid (by rw [ml];simp only [List.length_cons] at room;omega)]
      cases values evaluate cs <;> simp only [mapResult,PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,bind_tc_fail,bind_tc_div,bytes,hv,List.append_assoc]
#print axioms length
#print axioms complete
end R1Z.PV_RunJoin_ClaimImage48
