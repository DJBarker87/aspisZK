import Port4C_GeometryGroups
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_CollectStd
open Aeneas Aeneas.Std Result
variable {CoreError : Type}

def mapIterator {B I F Item : Type}
    (it : core.iter.traits.iterator.Iterator I Item) (f : core.ops.function.FnMut F Item B) :
    core.iter.traits.iterator.Iterator (core.iter.adapters.map.Map I F) B :=
  {next := OraclePortStdBuilder.mapNext it f}

def install (ops : Port3_NativeGeometryBody.Ops CoreError) : Port3_NativeGeometryBody.Ops CoreError :=
  {Port4C_GeometryGroups.install ops with
    op1 := OraclePortStdBuilder.iterMap
    mapIterator := mapIterator}

#print Aeneas.Std.alloc.vec.FromIteratorVec.from_iter
end AspisR1.Port4C_CollectStd
end
