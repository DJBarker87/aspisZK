# R438 generic FnMut bindings (literal LLBC inventory)

Input: the captured R438 LLBC, SHA-256 `76eefed780e23eb3243413b913e935dc7a9b661bceeb0fc0346668621ab07fb6`, produced with `has_errors=false` and the R438 command recorded alongside the capture.

The inventory preserves both raw hash-consed rows and decoded signatures/generics for the selected closure methods, trait rows, implementation rows, and relevant function calls. The observed function IDs are:

- `Fun24`: closure `FnMut::call_mut` shim; its body has a direct regular-function call to `Fun25`.
- `Fun25`: closure `Fn::call`; its body has a direct call to `Fun176`, the generic `core::slice::iter::Iterator::fold` body (`TraitImpl31`, trait 5, method 38).
- That `Fun25 -> Fun176` call supplies a trait reference to `TraitImpl47`, whose trait is `FnMut` (trait 9). Its regions are body regions 21, 22, and 32; its third type argument is closure environment `Type65` with body regions 21 and 22. The call's separately recorded closure-argument local type has its own region annotation; the exact raw values are preserved without asserting that the regions coincide.
- In `Fun176`, the callback invocation is a `Trait` function pointer with `Clause.Free(0)`, trait declaration 9 (`FnMut`), method slot 0, and method region `Body(16)`.
- The selected gamma closure has `Fun284`, source `TraitImpl47 / FnMut / method 0`; `TraitImpl47.methods[0]` points to it. The corresponding `FnOnce` function is `Fun283` at `TraitImpl46`, trait 0, method 0; `TraitImpl46.methods[0]` points to it. Trait declarations 0, 8, and 9 each contain their method slot in this generic capture.

`generic-binding-inventory.json` contains the complete captured rows and call arguments/generic substitutions, including the `Fun25 -> Fun176` call and `Fun176` callback call. This is a mechanical account of declarations, references, signatures, source spans and binder values. It does not infer runtime execution or prove Rust trait dispatch/source correspondence.
