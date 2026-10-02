# R204 vector extension extraction

The requested bounded Charon extraction succeeded with `--monomorphize` and all three requested `--include` selectors. It emitted a 160-function LLBC file with `has_errors=false`. Resource metrics and exact launcher/command/source assertions are in `R204-inventory.json`; the full command and `/usr/bin/time -v` output are preserved alongside the LLBC.

R204 makes the `Vec::extend` route inspectable: its structured body calls monomorphized `Vec::into_iter` (fun 49) and concrete `SpecExtend::spec_extend` (fun 50), both structured/transparent. The concrete body calls opaque `IntoIter::as_slice` (fun 91) and opaque `Vec::append_elements` (fun 92); additional intrinsic/drop declarations are listed in the JSON. This is an extraction inventory only. No Aeneas translation or Lean proof was run.
