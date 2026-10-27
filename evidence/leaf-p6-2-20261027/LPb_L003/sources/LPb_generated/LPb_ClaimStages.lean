import LPb_FoldStages
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
namespace LPb_ClaimStages
abbrev DotState := Option (fast_pairing.canonical.Dot × fast_pairing.canonical.Dot)
/-- Exact supplied model's scalar-decode/canonicality/two-Dot transition.
The native 29-push P6 equality remains OPEN, not assumed here. -/
def step {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array XRk_Wide 29#usize) (point : Nat) : DotState → Nat → Result DotState :=
  fun (state : Option (fast_pairing.canonical.Dot × fast_pairing.canonical.Dot)) l => do
    match state with
    | none => ok none
    | some (a,b) =>
      let scalar ← if point < 3 then do
          let row ← Array.index_usize sem.claims (XRk_usize point)
          Array.index_usize row (XRk_usize l)
        else if point = 3 then Array.index_usize sem.extra (XRk_usize l)
        else if point = 4 then Array.index_usize sem.before_z1 (XRk_usize l)
        else do
          let bytes ← XRk_sliceRange y1 (32*l) (32*l+32)
          let e ← aspis_core.field.wide_exact.WideExact.from_le_bytes bytes
          match e with
          | some e => ok (newQ e.c0)
          | none => fail .panic
      if !(scalar.c0.a < 2147483647#u32 && scalar.c0.b < 2147483647#u32 && scalar.c1.a < 2147483647#u32 && scalar.c1.b < 2147483647#u32) then ok none
      else do
        let v ← Array.index_usize g (XRk_usize l)
        let a ← fast_pairing.canonical.Dot.push a (XRk_toQ (newQ v.c0)) (XRk_toQ scalar)
        let b ← fast_pairing.canonical.Dot.push b (XRk_toQ (newQ v.c1)) (XRk_toQ scalar)
        ok (some (a,b))
def finish (state : DotState) : Result (Option XRk_Wide) := do
  match state with
  | none => ok none
  | some (a,b) => do
    let a ← XRk_dotFinish a
    let b ← XRk_dotFinish b
    ok (some (⟨oldQ a,oldQ b⟩ : XRk_Wide))
def sequence {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array XRk_Wide 29#usize) (point : Nat) : Result (Option XRk_Wide) := do
  let state ← (List.range 29).foldlM (step sem y1 g point) (some (XRk_dotZero,XRk_dotZero))
  finish state
theorem part_model_stages {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array XRk_Wide 29#usize) (point : Nat) :
    XRk_preparedPart sem y1 g point = sequence sem y1 g point := rfl

theorem stopped_step {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array XRk_Wide 29#usize) (point l : Nat) :
    step sem y1 g point none l = ok none := rfl
#print axioms part_model_stages
#print axioms stopped_step
end LPb_ClaimStages
