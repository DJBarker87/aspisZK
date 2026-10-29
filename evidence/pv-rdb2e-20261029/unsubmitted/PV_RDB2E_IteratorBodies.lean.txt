import R1Z.PV_RDB2E_Iterator
import R1Z.PV_RDB2D_DivisionRestoration
import R1Z.PV_RDB2D_CarryRestoration
namespace R1Z.PV_RDB2E_Iterator
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false

def divisionBody (q : Words) (r : U64) (j : Usize) :
    Result (ControlFlow (Words × U64 × Usize) (Words × U64)) := do
  let item ← nextBack q ⟨0#usize,j⟩
  match item with
  | none => ok (done (q,r))
  | some (word,h,c) => do
    let hi ← lift (U64.wrapping_shl r 32#u32)
    let lo ← lift (core.convert.num.FromU64U32.from word)
    let dividend ← lift (hi ||| lo)
    let p ← lift (core.convert.num.FromU64U32.from PV_B2_C_Sampler.aspis_core.field.P)
    let quotient ← dividend / p
    let replacement ← lift (UScalar.cast .U32 quotient)
    let q1 ← restore q h replacement
    let p1 ← lift (core.convert.num.FromU64U32.from PV_B2_C_Sampler.aspis_core.field.P)
    let r1 ← dividend % p1
    ok (cont (q1,r1,c.back))

def carryBody (q : Words) (n : U32) (i : Usize) :
    Result (ControlFlow (Words × U32 × Usize) (Words × U32)) := do
  let item ← next q ⟨i,8#usize⟩
  match item with
  | none => ok (done (q,n))
  | some (word,h,c) => do
    let a ← lift (core.convert.num.FromU64U32.from word)
    let b ← lift (core.convert.num.FromU64U32.from n)
    let sum ← lift (U64.wrapping_add a b)
    let p ← lift (core.convert.num.FromU64U32.from PV_B2_C_Sampler.aspis_core.field.P)
    let digit ← sum % p
    let replacement ← lift (UScalar.cast .U32 digit)
    let q1 ← restore q h replacement
    let p1 ← lift (core.convert.num.FromU64U32.from PV_B2_C_Sampler.aspis_core.field.P)
    let high ← sum / p1
    let n1 ← lift (UScalar.cast .U32 high)
    ok (cont (q1,n1,c.front))

theorem division_body (q : Words) (r : U64) (j : Usize) :
    divisionBody q r j=PV_RDB2D_SamplerRestoration.divisionBody q r j := by
  simp only [divisionBody,nextBack,restore,PV_RDB2D_SamplerRestoration.divisionBody,
    PV_RDB2D_SamplerRestoration.borrow,bind_assoc_eq,bind_tc_ok]
  split <;> simp only [bind_assoc_eq,bind_tc_ok,lift] <;> rfl

theorem carry_body (q : Words) (n : U32) (i : Usize) :
    carryBody q n i=PV_RDB2D_SamplerRestoration.carryBody q n i := by
  simp only [carryBody,next,restore,PV_RDB2D_SamplerRestoration.carryBody,
    PV_RDB2D_SamplerRestoration.borrow,bind_assoc_eq,bind_tc_ok]
  split <;> simp only [bind_assoc_eq,bind_tc_ok,lift] <;> rfl

#print axioms division_body
#print axioms carry_body
end R1Z.PV_RDB2E_Iterator
