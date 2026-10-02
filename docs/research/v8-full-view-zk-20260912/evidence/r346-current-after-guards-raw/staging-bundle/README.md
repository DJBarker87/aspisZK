# R346 after-guards callback suffix raw staging

This is uncompiled scratch staging from frozen R292 `Funs.input.lean` (SHA-256 `4d40a5b7b540adec90efef80a5ed8a5b4403704b388506af21f357761d95aec4`). The deterministic builder validates the frozen source inputs and extracts the exact contiguous block at original lines 527–605 inclusive. `selected-source-fragment.txt` preserves those source lines verbatim, including the final `ok (core.result.Result.Ok (ox2, oy2))`.

The wrapper uses the exact R292 `Error` doccomment, `@[discriminant isize]` attribute, inductive header, and seven constructors, copied into `AspisR346AfterGuardsRaw`. The wrapper's inner error parameter is this namespaced declaration. The selected suffix only constructs `core.result.Result.Ok`; it does not construct an inner error, and no equivalence with another `Error` declaration is claimed. The prior R156 binding candidate and its complete evidence remain byte-exact under `history/initial-error-binding/`.

`core.slice.Slice.last` is explicitly imported and opened from `AspisR316SliceLastRaw`, whose actual emitted definition and binding audit are copied under `provenance/`. This avoids relying on an `open` directive from the R318 import. The audit records the R316 source span and its one generated API-name adapter; the source body is otherwise unchanged.

The selected block starts inside the validated `else` branch, after source checks for nonempty inputs and the chained iterator predicate. It excludes those checks and the `b2` branch returning `Error.Domain`; this wrapper makes no full-callback guard claim. The source operations in the selected block remain unchanged.

The Lean file emits `#print axioms Error` and `#print axioms selectedAfterGuards`. No Lean compile or axioms output was run. The scratch audit records the exact source, fragment, local Error declaration, R316 binding, and generated wrapper hashes.
