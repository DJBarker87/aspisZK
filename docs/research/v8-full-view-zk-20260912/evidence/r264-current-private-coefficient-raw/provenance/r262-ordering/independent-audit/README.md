# Independent R262 private coefficient ordering audit

The checker verifies the exact R261 input SHA-256 and expected R262 output SHA-256, independently decodes hash-consed LLBC values, and traverses typed ADT/function/global references from Fun0 and Fun1. It checks both roots are local function bodies named `new` and `four`, compares all input JSON after removing only `translated.ordered_decls`, and independently validates dependency order, declaration closure, cycles, trait references, and integer-ID census against the generator's audit.

The audited closure has 45 declarations: 11 Type, 31 Fun, and 3 Global, with 111 typed dependency edges. All dependencies precede their users; no missing references, cycles, or trait references were found. The full JSON and all declaration rows remain unchanged apart from order metadata.

Structural ordering only; no translation or source-semantics claim.
