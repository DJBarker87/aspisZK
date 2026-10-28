import NDH_Reference.Funs
import AdapterRwModel
set_option autoImplicit false
namespace NDH_RegistryPrimitives
open Aeneas Aeneas.Std Result AdapterRw
open aspis_statement.pool_v1.verifier_registry

def noRetirementV1 (r : VerifierRegistryEntryV1) : Result Bool :=
  NDH_Reference.retirement_ref r.retirement_slot

def noRetirementV2 (r : VerifierRegistryEntryV2) : Result Bool :=
  NDH_Reference.retirement_ref r.retirement_slot

theorem retirement_v1 (r : VerifierRegistryEntryV1) :
    noRetirementV1 r=ok (decide (r.retirement_slot=core.num.U64.MAX)) := rfl

theorem retirement_v2 (r : VerifierRegistryEntryV2) :
    noRetirementV2 r=ok (decide (r.retirement_slot=core.num.U64.MAX)) := rfl

def status (v : U8) : Result (core.result.Result VerifierEntryStatusV1 PoolV1VerifierRegistryFormatError) := do
  let r ← NDH_Reference.status_ref v
  ok (match r with
    | none => .Err .InvalidStatus
    | some i => if i=0#u8 then .Ok .Pending else
                if i=1#u8 then .Ok .Active else
                if i=2#u8 then .Ok .Paused else .Ok .Retired)

theorem pending : status 0#u8=ok (.Ok .Pending) := rfl

theorem active : status 1#u8=ok (.Ok .Active) := rfl

theorem paused : status 2#u8=ok (.Ok .Paused) := rfl

theorem retired : status 3#u8=ok (.Ok .Retired) := rfl

theorem invalid (v : U8) (h0 : v≠0#u8) (h1 : v≠1#u8)
    (h2 : v≠2#u8) (h3 : v≠3#u8) : status v=ok (.Err .InvalidStatus) := by
  have n0 : v.val≠0 := by intro h; apply h0; exact UScalar.eq_of_val_eq h
  have n1 : v.val≠1 := by intro h; apply h1; exact UScalar.eq_of_val_eq h
  have n2 : v.val≠2 := by intro h; apply h2; exact UScalar.eq_of_val_eq h
  have n3 : v.val≠3 := by intro h; apply h3; exact UScalar.eq_of_val_eq h
  unfold status NDH_Reference.status_ref
  split
  · exact False.elim (n0 rfl)
  · exact False.elim (n1 rfl)
  · exact False.elim (n2 rfl)
  · exact False.elim (n3 rfl)
  · rfl

#print axioms retirement_v1
#print axioms retirement_v2
#print axioms pending
#print axioms active
#print axioms paused
#print axioms retired
#print axioms invalid
end NDH_RegistryPrimitives
