import R1Z.PV_RunJoin_ArrayUpdatePrefix50
import R1Z.PV_RunJoin_Vector44
import R1Z.PV_RunJoin_ResultMap50
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PrefixFold50
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightMap46 (mapResult)

def image {A B : Type} (f : A → B) (a : Array A 1024#usize) : alloc.vec.Vec B :=
  ⟨a.val.map f,by rw [List.length_map,a.property];scalar_tac⟩

def arrayRun {A : Type} (cell : Usize → Result A) : Nat → Array A 1024#usize → Usize → Result (Array A 1024#usize)
  | 0,a,_ => ok a
  | n+1,a,row => do
    let value ← cell row
    let next ← Array.update a row value
    arrayRun cell n next (Usize.wrapping_add row 1#usize)

def vecRun {B : Type} (cell : Usize → Result B) : Nat → alloc.vec.Vec B → Usize → Result (alloc.vec.Vec B)
  | 0,out,_ => ok out
  | n+1,out,row => do
    let value ← cell row
    let next ← alloc.vec.Vec.push out value
    vecRun cell n next (Usize.wrapping_add row 1#usize)

theorem complete {A B : Type} (f : A → B) (cell : Usize → Result A)
    (n : Nat) (a : Array A 1024#usize) (out : alloc.vec.Vec B) (row : Usize)
    (bound : row.val+n=1024) (hprefix : out.val=(a.val.take row.val).map f) :
    vecRun (fun i => mapResult f (cell i)) n out row=
      mapResult (image f) (arrayRun cell n a row) := by
  induction n generalizing a out row with
  | zero =>
    have all : a.val.length≤row.val := by rw [a.property];change 1024≤row.val;omega
    rw [List.take_of_length_le all] at hprefix
    change ok out=ok (image f a)
    apply congrArg Result.ok
    exact Subtype.ext hprefix
  | succ n ih =>
    have hi : row.val<(1024#usize).val := by change row.val<1024;omega
    have len : out.length=row.val := by
      change out.val.length=row.val
      rw [hprefix,List.length_map,List.length_take,a.property]
      change min row.val 1024=row.val
      omega
    have inc := PV_RunJoin_MergeLoop35.increment row (by omega)
    cases result : cell row with
    | fail e => simp only [vecRun,arrayRun,result,mapResult,PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_fail]
    | div => simp only [vecRun,arrayRun,result,mapResult,PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_div]
    | ok value =>
      obtain ⟨nextA,ha,hpa⟩ := PV_RunJoin_ArrayUpdatePrefix50.complete a row value hi
      obtain ⟨nextV,hv,hpv⟩ := PV_RunJoin_Vector44.push out (f value) (by rw [len];scalar_tac)
      have nextPrefix : nextV.val=(nextA.val.take (Usize.wrapping_add row 1#usize).val).map f := by
        rw [inc,hpa,List.map_append,List.map_singleton,hpv,hprefix]
      simp only [vecRun,arrayRun,result,mapResult,PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,ha,hv]
      exact ih nextA nextV _ (by rw [inc];omega) nextPrefix
#print axioms image
#print axioms arrayRun
#print axioms vecRun
#print axioms complete
end R1Z.PV_RunJoin_PrefixFold50
