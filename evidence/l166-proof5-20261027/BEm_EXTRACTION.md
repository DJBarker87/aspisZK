# Extraction attempts (four-invocation budget exhausted)

C01: pinned Charon succeeded, 1,222,748-byte nonempty LLBC. Includes BEm_extract namespace; remaining crate functions opaque. A01 failed in InterpBorrows.ml:2731 at original owned reference batch range loop. No Lean body emitted.

C02: split the three-tree range loop into three explicit calls and broadened include to crate. This was a selector mistake: include crate did not override opaque crate; the only extracted root has no body. A02 exit0 generated an EMPTY Funs.lean and an external template axiom. Both are EXCLUDED. Raw generated files retained as .lean.txt, never imported or compiled; no external template is filled or accepted.

There is no BEm_ModelAgreement theorem and no complete reference extraction. The successful translator exit is not a semantic result. No additional invocation is authorized. Tool rebuilding and translator patches were not attempted. Continue independent P6/Kani work; do not treat this as physical association.
