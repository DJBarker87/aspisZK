import PV_B1_Carrier230
import PV_B1_SumNative
set_option autoImplicit false
noncomputable section
namespace PV_B1_HostSumValue
open Aeneas Aeneas.Std PV_B1_Carrier230

def zero : HQ := { c0 := {a:=0#u32,b:=0#u32},c1 := {a:=0#u32,b:=0#u32} }
def add (a b : HQ) : HQ :=
  { c0 := { a:=PV_B1_SumNative.limbAdd a.c0.a b.c0.a, b:=PV_B1_SumNative.limbAdd a.c0.b b.c0.b },
    c1 := { a:=PV_B1_SumNative.limbAdd a.c1.a b.c1.a, b:=PV_B1_SumNative.limbAdd a.c1.b b.c1.b } }

theorem to_zero : toQ zero=PV_B1_230.aspis_core.field.QM31.ZERO := by
  unfold toQ zero PV_B1_230.aspis_core.field.QM31.ZERO
  rfl

theorem to_add (a b : HQ) : toQ (add a b)=PV_B1_SumNative.add (toQ a) (toQ b) := rfl

theorem fold (xs : List HQ) (acc : HQ) :
    fromQ ((xs.map toQ).foldl PV_B1_SumNative.add (toQ acc))=xs.foldl add acc := by
  induction xs generalizing acc with
  | nil => simp only [List.map_nil,List.foldl_nil,from_to]
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [←to_add,ih]
#print axioms to_zero
#print axioms to_add
#print axioms fold
end PV_B1_HostSumValue
