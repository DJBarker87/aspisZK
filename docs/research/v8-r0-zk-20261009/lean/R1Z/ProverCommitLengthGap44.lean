import R1Z.ProverCommitTrustedStd24
/-! Interface non-implication, not a counterexample to Rust BTreeMap.
The accepted API does not expose native len. Keeping every accepted field
and map state fixed, an unconstrained reported length changes the native
root guard. Defining that report as decoded cardinality would add exactly
the missing source law rather than prove it. -/
set_option autoImplicit false
namespace R1Z.ProverCommitLengthGap44
open ProverCommitTrustedStd24
abbrev Tree := Std.TreeMap Nat Nat compare

def singleton (root : Nat) : Tree := (∅ : Tree).insert 0 root

def guard (reportedLength : Tree → Nat) (level : Tree) (root : Nat) : Bool :=
  reportedLength level == 1 && (modelMap (cmp := compare)).get level 0 == some root

/-- All nine accepted TrustedStd fields hold for the same map/TLS instance.
An otherwise unconstrained source length can still change success to Merkle
error on an identical singleton, root and get result. -/
theorem length_not_determined (root : Nat) :
    TrustedStd (modelMap (Key := Nat) (Value := Nat) (cmp := compare))
      (modelTLS (Thread := Unit) (Slot := Unit) (Output := Unit)) () [] ∧
    guard (fun _ => 0) (singleton root) root = false ∧
    guard (fun _ => 1) (singleton root) root = true := by
  refine ⟨model_consistent (), ?_, ?_⟩
  · rfl
  · simp [guard,modelMap,singleton]

#print axioms length_not_determined
end R1Z.ProverCommitLengthGap44
