# Stage-2 checkpoint reader source leaf

PROVED universal source-body invariants: successful `Reader::raw(N)` retains the input byte slice and advances its cursor through the same checked `at + N` result; successful `Reader::e` / `k` has a successful raw read of 32 / 16 bytes and a successful decoder returning that same value, with the cursor/input invariants retained.

Actual adopted-source raw/e/k bodies were extracted successfully by Charon and Aeneas through public extraction-entry wrappers. The wrapper adapter is not production code. Full `resume` extraction separately fails with an escaping mutable-region error and remains OPEN.

The Lean elaboration adapter removes generated resource overrides; E/K decoders and array `unwrap` are explicit arbitrary function parameters. The `unwrap` boundary avoids admitting the historical Aeneas `core.fmt.Formatter` opaque declaration. This does **not** prove that arbitrary unwrap preserves slice bytes, strict field-decoder correctness, whole checkpoint reconstruction, or caller provenance. Those joins remain OPEN. Generic `Option.ok_or` is reused verbatim from the existing DecodeKFullV10 extraction, with an exact source pin. No opaque template is imported.

Focused types/body/proof targets passed under -M4400,1GiB high/2GiB max/swap0 scopes. All theorem axiom reports contain only standard axioms. Exact targets, source/import/compiler pins, timings and process/cgroup RSS are retained. No binaries. The types target was reused unchanged from the preceding focused attempt; only changed body and theorem were checked again.
