import NDO_NBN_AccountCallbackObstruction
import PoolS2_PolicySource
set_option autoImplicit false
noncomputable section
namespace NBX_SlotValues
open Aeneas Aeneas.Std Result AspisR1
open AdapterRw.aspis_statement.pool_v1.verifier_registry

/-- These value functions are candidates for the existing missing adapter fields.
Native credit requires the paired actual Rust gates and caller association;
this module alone makes no AeneasExtraction claim. -/
def op25 (r : VerifierRegistryV1) : Result Bool := ok (r.flags &&& 1#u8 != 0#u8)
def op26 (r : VerifierRegistryV1) : Result Bool := ok (r.flags &&& 2#u8 != 0#u8)
def op27 (r : VerifierRegistryV2) : Result Bool := ok (r.flags &&& 1#u8 != 0#u8)
def op28 (r : VerifierRegistryV2) : Result Bool := ok (r.flags &&& 2#u8 != 0#u8)
def activeStatus : VerifierEntryStatusV1 → Bool
  | .Active => true
  | _ => false

def active (status : VerifierEntryStatusV1) (activation retirement slot : U64) : Bool :=
  activeStatus status && decide (activation ≤ slot) &&
    (decide (retirement = 18446744073709551615#u64) || decide (slot < retirement))
def op29 (r : VerifierRegistryEntryV2) (slot : U64) : Result Bool :=
  ok (active r.status r.activation_slot r.retirement_slot slot)
def op30 (r : VerifierRegistryEntryV1) (slot : U64) : Result Bool :=
  ok (active r.status r.activation_slot r.retirement_slot slot)

/-- Update existing fields only; no law, new dictionary carrier or success
hypothesis is added. Other adapter fields retain their original values. -/
def instantiate (base : AdapterRw.Ops) : AdapterRw.Ops :=
  {base with
    op15 := PoolS2_PolicySource.pool_v1.format.validate_verifier_policy_v1
    op25 := op25
    op26 := op26
    op27 := op27
    op28 := op28
    op29 := op29
    op30 := op30}

theorem selected {F E : Type} (c : DrvC_Installation.Configuration F E) :
    let d := {c with adapter := instantiate c.adapter}
    (DrvC_Installation.sdk d).op15 =
      PoolS2_PolicySource.pool_v1.format.validate_verifier_policy_v1 ∧
    (DrvC_Installation.sdk d).op25 = op25 ∧
    (DrvC_Installation.sdk d).op26 = op26 ∧
    (DrvC_Installation.sdk d).op27 = op27 ∧
    (DrvC_Installation.sdk d).op28 = op28 ∧
    (DrvC_Installation.sdk d).op29 = op29 ∧
    (DrvC_Installation.sdk d).op30 = op30 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Every return, including rejection/divergence, comes from that one function.
The frame parameter is arbitrary and neither read nor changed by the value call.
This is a value/frame composition lemma, not a native heap admission. -/
theorem frame {A B S : Type} (f : A → Result B) (a : A) (s : S) :
    (do let b ← f a; ok (b,s)) = (match f a with
      | .ok b => ok (b,s)
      | .fail e => .fail e
      | .div => .div) := by
  cases h : f a <;> rfl

/-- Reached SDK calls consume exactly the selected result at the same input;
there is no successful-result hypothesis and no second output witness. -/
theorem call25 {F E B : Type} (c : DrvC_Installation.Configuration F E)
    (r : VerifierRegistryV1) (k : Bool → Result B) :
    (do let b ← (DrvC_Installation.sdk {c with adapter := instantiate c.adapter}).op25 r
        k b) = (do let b ← op25 r; k b) := rfl

theorem call29 {F E B : Type} (c : DrvC_Installation.Configuration F E)
    (r : VerifierRegistryEntryV2) (slot : U64) (k : Bool → Result B) :
    (do let b ← (DrvC_Installation.sdk {c with adapter := instantiate c.adapter}).op29 r slot
        k b) = (do let b ← op29 r slot; k b) := rfl

theorem call26 {F E B : Type} (c : DrvC_Installation.Configuration F E)
    (r : VerifierRegistryV1) (k : Bool → Result B) :
    (do let b ← (DrvC_Installation.sdk {c with adapter := instantiate c.adapter}).op26 r
        k b) = (do let b ← op26 r; k b) := rfl

theorem call27 {F E B : Type} (c : DrvC_Installation.Configuration F E)
    (r : VerifierRegistryV2) (k : Bool → Result B) :
    (do let b ← (DrvC_Installation.sdk {c with adapter := instantiate c.adapter}).op27 r
        k b) = (do let b ← op27 r; k b) := rfl

theorem call28 {F E B : Type} (c : DrvC_Installation.Configuration F E)
    (r : VerifierRegistryV2) (k : Bool → Result B) :
    (do let b ← (DrvC_Installation.sdk {c with adapter := instantiate c.adapter}).op28 r
        k b) = (do let b ← op28 r; k b) := rfl

theorem call30 {F E B : Type} (c : DrvC_Installation.Configuration F E)
    (r : VerifierRegistryEntryV1) (slot : U64) (k : Bool → Result B) :
    (do let b ← (DrvC_Installation.sdk {c with adapter := instantiate c.adapter}).op30 r slot
        k b) = (do let b ← op30 r slot; k b) := rfl

theorem call15 {F E B : Type} (c : DrvC_Installation.Configuration F E)
    (p : AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1)
    (k : core.result.Result Unit AdapterRw.aspis_statement.pool_v1.format.PoolV1FormatError → Result B) :
    (do let r ← (DrvC_Installation.sdk {c with adapter := instantiate c.adapter}).op15 p
        k r) = (do let r ← PoolS2_PolicySource.pool_v1.format.validate_verifier_policy_v1 p; k r) := rfl

#print axioms selected
#print axioms frame
#print axioms call25
#print axioms call29
#print axioms call26
#print axioms call27
#print axioms call28
#print axioms call30
#print axioms call15
end NBX_SlotValues
end
