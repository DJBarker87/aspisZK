import SDY_Join_PublicModel
open Aeneas Aeneas.Std Result ControlFlow Error
open SDY_Join_Release SDY_Join_FieldExternal
/- state_only_hiding.rs selected_mask_value mathematical model, frozen disjoint
   exponent schedules and tower coordinates. Arithmetic/source P6 OPEN. -/
def SDY_Join_basis (i : Nat) : aspis_core.field.QM31 :=
  match i%4 with
  | 0 => qone
  | 1 => ⟨⟨0#u32,1#u32⟩,⟨0#u32,0#u32⟩⟩
  | 2 => ⟨⟨0#u32,0#u32⟩,⟨1#u32,0#u32⟩⟩
  | _ => ⟨⟨0#u32,0#u32⟩,⟨0#u32,1#u32⟩⟩
def SDY_Join_scaleQ (q : aspis_core.field.QM31) (n : U32) : Result aspis_core.field.QM31 :=
  aspis_core.field.QM31.mul q ⟨⟨n,0#u32⟩,⟨0#u32,0#u32⟩⟩
def aspis_core.state_only_hiding.state_only_selected_mask_value
    (c1 : Array aspis_core.field.QM31 16#usize)
    (masks : Array aspis_core.field.QM31 10#usize)
    (explicit : aspis_core.field.QM31) (point : Array aspis_core.field.QM31 10#usize) :
    Result aspis_core.field.QM31 := do
  let (suffix,weighted) ← ((List.range 10).reverse).foldlM (fun (s,w) i => do
    let v ← Array.index_usize point (SDY_Join_usize i)
    let s ← aspis_core.field.QM31.add s v
    let w ← if i = 0 then ok w else aspis_core.field.QM31.add w s
    ok (s,w)) (qzero,qzero)
  let a ← SDY_Join_scaleQ suffix 3#u32
  let b ← SDY_Join_scaleQ weighted 22#u32
  let linear ← aspis_core.field.QM31.add a b
  let a ← SDY_Join_scaleQ suffix 275#u32
  let b ← SDY_Join_scaleQ weighted 150#u32
  let explicitLinear ← aspis_core.field.QM31.add a b
  let exponents := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25]
  let maskExponents := [1,3,5,7,9,11,15,17,19,21]
  let coefficients ← (List.range 27).mapM fun e => do
    match (List.range 16).find? (fun i => exponents[i]?.getD 27 = e) with
    | some i =>
      let v ← Array.index_usize c1 (SDY_Join_usize i)
      aspis_core.field.QM31.mul v (SDY_Join_basis i)
    | none =>
      match (List.range 10).find? (fun i => maskExponents[i]?.getD 27 = e) with
      | some i =>
        let v ← Array.index_usize masks (SDY_Join_usize i)
        aspis_core.field.QM31.mul v (SDY_Join_basis i)
      | none => ok qzero
  let shared ← coefficients.reverse.foldlM (fun a c => do
    let a ← aspis_core.field.QM31.mul a linear
    aspis_core.field.QM31.add a c) qzero
  let power ← SDY_Join_qpow explicitLinear 26
  let factor ← aspis_core.field.QM31.add qone power
  let term ← aspis_core.field.QM31.mul factor explicit
  aspis_core.field.QM31.add shared term
