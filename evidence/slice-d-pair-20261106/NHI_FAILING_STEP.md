# NHI excluded/failing attempts

- NHE L077 (predecessor): default recursion depth on whole closure rfl. Replaced by isolated NHI_ScalarStep.cell_bind and emitted, L003 exit0. No depth increase.
- NHI L001: isolated bind simplification left reducible tuple lets; L002 tried dsimp but made no progress; L003 added final shallow rfl and passes. No success premise.
- NHI L006: spacing in a ≤ inequality parsed as another token, plus wrapping numeral not reduced. Corrected exact inequality and explicit Nat wrapping-add goal; L007 passes.
- NHI L008/L009: absent CM31.ZERO constant then opaque canonE prevented Decidable synthesis. Exact canonical-predicate reduction added; L010 passes. No axiom or metric change.
- NHI K009: tool input compile error E0277: frozen QM31 has no kani::Arbitrary implementation. No verification reached; no native credit. Fixed owned input construction to q(kani::any::<[u32;4]>()) per array cell, preserving the identical arbitrary-word domain. New attempt uses corrected source under the original g04 name; never an unchanged rerun or a rename to change a verdict.
