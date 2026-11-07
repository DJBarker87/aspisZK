import LIB_VCarriers
import NFW_PreparedPort
set_option autoImplicit false
noncomputable section
namespace LIBC_VStateCarriers
open Aeneas Aeneas.Std
abbrev q := AspisR1.NFW_PreparedPort.q
abbrev e := AspisR1.NFW_PreparedPort.e
def fromQ (x : AspisR1Stage2.aspis_core.field.QM31) : AspisR1PublicPreparation.aspis_core.field.QM31 :=
 ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromE (x : AspisR1Stage2.aspis_core.field.wide_exact.WideExact) : AspisR1PublicPreparation.aspis_core.field.WideExact :=
 ⟨fromQ x.c0,fromQ x.c1⟩
def mapVec {A B : Type} (f : A → B) (x : alloc.vec.Vec A) : alloc.vec.Vec B :=
 ⟨x.val.map f,by simpa only [List.length_map] using x.property⟩
def toAcc (a : LIB_VCarriers.Acc) : AspisR1Stage2.verifier.Accumulator :=
 ⟨mapVec q a.weights,e a.rhs,q a.power,a.next⟩
def fromAcc (a : AspisR1Stage2.verifier.Accumulator) : LIB_VCarriers.Acc :=
 ⟨mapVec fromQ a.weights,fromE a.rhs,fromQ a.power,a.next⟩
theorem from_to_q (x : AspisR1PublicPreparation.aspis_core.field.QM31) : fromQ (q x) = x := by cases x;rfl
theorem to_from_q (x : AspisR1Stage2.aspis_core.field.QM31) : q (fromQ x) = x := by cases x;rfl
theorem from_to_e (x : AspisR1PublicPreparation.aspis_core.field.WideExact) : fromE (e x) = x := by cases x;rfl
theorem to_from_e (x : AspisR1Stage2.aspis_core.field.wide_exact.WideExact) : e (fromE x) = x := by cases x;rfl
theorem from_to_acc (a : LIB_VCarriers.Acc) : fromAcc (toAcc a) = a := by
 cases a with
 | mk weights rhs power next =>
  unfold fromAcc toAcc
  congr 1
  · apply Subtype.ext
    change (weights.val.map q).map fromQ = weights.val
    simp only [List.map_map,Function.comp_def,from_to_q]
    exact List.map_id weights.val
theorem to_from_acc (a : AspisR1Stage2.verifier.Accumulator) : toAcc (fromAcc a) = a := by
 cases a with
 | mk weights rhs power next =>
  unfold fromAcc toAcc
  congr 1
  · apply Subtype.ext
    change (weights.val.map fromQ).map q = weights.val
    simp only [List.map_map,Function.comp_def,to_from_q]
    exact List.map_id weights.val
theorem weights_length (a : LIB_VCarriers.Acc) : (toAcc a).weights.val.length = a.weights.val.length :=
 List.length_map _
#print axioms from_to_q
#print axioms to_from_q
#print axioms from_to_e
#print axioms to_from_e
#print axioms from_to_acc
#print axioms to_from_acc
#print axioms weights_length
end LIBC_VStateCarriers
