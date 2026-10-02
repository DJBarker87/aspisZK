# R207 vector copy extraction

The bounded Charon extraction succeeded with the two requested added includes and unchanged R204 source/flag assertions, release settings, and memory caps. It emitted 166 functions with `has_errors=false`; no Aeneas translation was run. Command, resource report, launcher, source hashes, and revision are recorded in `R207-inventory.json`.

In the extracted structured body, concrete `SpecExtend::spec_extend` fun 50 calls `IntoIter::as_slice` fun 91 and `Vec::append_elements` fun 92. `as_slice` is now structured and exposes a `PtrFromParts` operation plus a Foreign/Opaque precondition check. `append_elements` is structured and exposes reserve, a `CopyNonOverlapping` operation, and its Foreign/Opaque precondition check. The source uses a direct length-field increment (`self.len += count`), not a `set_len` method call. See the inventory for IDs and body opacity; no source semantics or pointer-refinement conclusion is drawn.
