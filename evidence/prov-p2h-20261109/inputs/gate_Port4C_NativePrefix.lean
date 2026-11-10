import Port4C_GeometryFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_NativePrefix
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
structure Leaves where
  mul : U32 → U32 → Result U32
  one : Result U32

/-- [aspis_r1_cost_probe::verifier::batch_prefix_products]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 138:4-143:5 -/
@[rust_loop_body]
def verifier.batch_prefix_products_loop.body (ops : Leaves)
  (flat : Slice aspis_core.field.M31)
  (prefixes : alloc.vec.Vec aspis_core.field.M31)
  (product : aspis_core.field.M31) (index : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) ×
    aspis_core.field.M31 × Std.Usize) ((alloc.vec.Vec aspis_core.field.M31) ×
    aspis_core.field.M31))
  := do
  let i := Slice.len flat
  if index < i
  then
    let value ← Slice.index_usize flat index
    let prefixes1 ← alloc.vec.Vec.push prefixes product
    let product1 ← ops.mul product value
    let index1 ← lift (Std.Usize.wrapping_add index 1#usize)
    ok (cont (prefixes1, product1, index1))
  else ok (done (prefixes, product))

/-- [aspis_r1_cost_probe::verifier::batch_prefix_products]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 138:4-143:5 -/
@[rust_loop]
def verifier.batch_prefix_products_loop (ops : Leaves)
  (flat : Slice aspis_core.field.M31)
  (prefixes : alloc.vec.Vec aspis_core.field.M31)
  (product : aspis_core.field.M31) (index : Std.Usize) :
  Result ((alloc.vec.Vec aspis_core.field.M31) × aspis_core.field.M31)
  := do
  loop
    (fun (prefixes1, product1, index1) =>
      (verifier.batch_prefix_products_loop.body ops) flat prefixes1 product1 index1)
    (prefixes, product, index)

/-- [aspis_r1_cost_probe::verifier::batch_prefix_products]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 134:0-145:1 -/
def verifier.batch_prefix_products (ops : Leaves)
  (flat : Slice aspis_core.field.M31) :
  Result ((alloc.vec.Vec aspis_core.field.M31) × aspis_core.field.M31)
  := do
  let i := Slice.len flat
  let prefixes := alloc.vec.Vec.with_capacity aspis_core.field.M31 i
  let product ← ops.one
  (verifier.batch_prefix_products_loop ops) flat prefixes product 0#usize

#print axioms verifier.batch_prefix_products_loop.body
#print axioms verifier.batch_prefix_products_loop
#print axioms verifier.batch_prefix_products
end AspisR1.Port4C_NativePrefix
end
