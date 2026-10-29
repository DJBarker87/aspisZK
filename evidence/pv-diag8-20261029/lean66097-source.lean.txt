import PV_DIAG8_AuditValue
import PV_DIAG8_Arrays
set_option autoImplicit false
namespace PV_DIAG8
abbrev DIAG8Inputs := List String × List (List Nat) × History

def publicInputs {P : Type} (messages : P → List ClientGuard)
    (path : P → List PathStep) (stack : P → List Nat)
    (requests : P → List Request) (world : History → Request → Reply) (p : P) : DIAG8Inputs :=
  ((messages p).map guardText,captures (stack p) (path p),replay world [] (requests p))

/-- Local sufficient handoff. Binding is an OPEN native premise, displayed
explicitly; this theorem does not establish the whole DIAG_* native instance. -/
theorem DIAG8_inputs_given_native_binding {P W O : Type}
    (native : P → W → DIAG8Inputs) (decode : DIAG8Inputs → O)
    (messages : P → List ClientGuard) (path : P → List PathStep)
    (stack : P → List Nat) (requests : P → List Request)
    (world : History → Request → Reply)
    (sourceBinding : ∀ p w, native p w = publicInputs messages path stack requests world p)
    (p : P) (w w' : W) : decode (native p w) = decode (native p w') := by
  rw [sourceBinding,sourceBinding]
#print axioms DIAG8_inputs_given_native_binding

/-- The entire family of finite coordinates is retained, not only one prefix.
Native divergent/abnormal traces still need their association with this family. -/
theorem DIAG8_prefix_family {P W O : Type}
    (native : P → W → Nat → DIAG8Inputs) (decode : DIAG8Inputs → O)
    (publicFamily : P → Nat → DIAG8Inputs)
    (sourceBinding : ∀ p w n, native p w n = publicFamily p n)
    (p : P) (w w' : W) :
    (fun n => decode (native p w n)) = (fun n => decode (native p w' n)) := by
  funext n
  rw [sourceBinding,sourceBinding]
#print axioms DIAG8_prefix_family
/-- The selected audit field can be added to any already-public decoded
prefix without introducing witness data; this does not establish that prefix. -/
theorem DIAG8_audit_joint {O : Type} (decode : O × MaskAudit → String)
    (output output' : O) (same : output=output')
    (a b x y : MaskAudit) (hx : auditGate a=some x) (hy : auditGate b=some y) :
    decode (output,x)=decode (output',y) := by
  rw [same,audit_success_literal a x hx,audit_success_literal b y hy]
#print axioms DIAG8_audit_joint
end PV_DIAG8
