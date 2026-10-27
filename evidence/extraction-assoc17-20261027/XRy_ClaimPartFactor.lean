import XRy_ClaimSelectExtra
open Aeneas Aeneas.Std Result
open XRn_Join_Release XRn_Join_FieldExternal
set_option autoImplicit false
namespace XRy_ClaimPartFactor

theorem factor {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
 (g : Array XRn_Join_Wide 29#usize) (point : Nat) :
 XRn_Join_preparedPart sem y1 g point = (
do
  let state ← (List.range 29).foldlM (fun (state : Option (fast_pairing.canonical.Dot × fast_pairing.canonical.Dot)) l => do
    match state with
    | none => ok none
    | some (a,b) =>
      let scalar ← XRy_ClaimSelect.read sem y1 point l
      if !(scalar.c0.a < 2147483647#u32 && scalar.c0.b < 2147483647#u32 && scalar.c1.a < 2147483647#u32 && scalar.c1.b < 2147483647#u32) then ok none
      else do
        let v ← Array.index_usize g (XRn_Join_usize l)
        let a ← fast_pairing.canonical.Dot.push a (XRn_Join_toQ (newQ v.c0)) (XRn_Join_toQ scalar)
        let b ← fast_pairing.canonical.Dot.push b (XRn_Join_toQ (newQ v.c1)) (XRn_Join_toQ scalar)
        ok (some (a,b))) (some (XRn_Join_dotZero,XRn_Join_dotZero))
  match state with
  | none => ok none
  | some (a,b) => do
    let a ← XRn_Join_dotFinish a
    let b ← XRn_Join_dotFinish b
    ok (some (⟨oldQ a,oldQ b⟩ : XRn_Join_Wide))) := by rfl

#print axioms factor
end XRy_ClaimPartFactor
