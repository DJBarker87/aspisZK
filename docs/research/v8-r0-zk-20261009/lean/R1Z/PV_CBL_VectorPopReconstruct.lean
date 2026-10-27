import R1Z.PV_CBL_VectorPopSpec
namespace R1Z.PV_CBL_VectorPopReconstruct
set_option autoImplicit false

theorem list {T : Type} (xs : List T) : xs.dropLast++xs.getLast?.toList=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      simpa only [List.dropLast_cons_cons,List.getLast?_cons_cons,List.cons_append]
        using congrArg (List.cons x) ih

theorem vector {T : Type} (v : Aeneas.Std.alloc.vec.Vec T) :
    (PV_CBL_VectorPopSpec.pop v).2.val++(PV_CBL_VectorPopSpec.pop v).1.toList=v.val :=
  list v.val
#print axioms list
#print axioms vector
end R1Z.PV_CBL_VectorPopReconstruct
