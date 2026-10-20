# Emitted EbyEDot.push source adapter and count consumer

The first Lean module defines the exact selected generated EbyEDot.push bind/branch sequence with four explicit substitutions: MAX_TERMS to maxTerm; Q::from_wide to an explicit fromWide; Dot::push to explicit pushDot; checked count addition to explicit addUsize. A theorem proves definitionally that this port equals the parameterized schedule used by the four-Dot proof. The source checker verifies the generated Funs body matches this port after precisely those substitutions.

The second module composes the port with the exact copied to_limbs/Q::from_wide sequence (proved equal to the retained EbyK coordinate converter) and the existing raw Dot backend. For any successful selected-source push under the four-Dot accumulator invariant, it derives the successor count/range invariant and all four raw-result state updates without assuming the handwritten schedule or a separate fromWide success relation.

This remains scoped to a successful parameterized source port. The checker establishes the exact generated-body port, and the fromWide bridge establishes its concrete EbyK coordinate implementation. The imported raw Dot backend uses the selected Dot-push proof. No whole EbyE caller, complete EbyE product, or production source-runtime claim is made.
