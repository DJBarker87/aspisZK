# Indexed `add_small_base_p` candidate proof cone

This source-only packet collects the focused Aeneas extraction and native Lean checks for an indexed-loop candidate of `add_small_base_p`. The Rust production file is unchanged. The candidate is not adopted and this packet establishes no production sampler-law or density result.

The candidate replaces the production `for digit in digits` traversal with an explicit `usize` index loop, retaining the same per-digit `sum`, `% P` digit update, `/ P` carry, final debug assertion, and boolean result. The exact candidate input is under `extraction/candidate-input/`; the unchanged production sampler snapshot and two small function diffs are under `extraction/production-source/` and `source-diffs/`. Source hashes and line spans are recorded in `manifest.json` and the copied source-pins files.

The checked proof chain is:

1. Candidate Aeneas-generated `Types` and `Funs`, mechanically moved to a distinct module path/namespace and stripped of generated heartbeat/depth settings. The exact raw and renamed files plus successful native receipts are retained.
2. The generated indexed-loop one-step theorem, including successful U64 arithmetic and the updated-array write at each index.
3. The canonical loop theorem, by induction over the remaining index range.
4. The Nat-model theorem, relating the same loop execution to `addDigits` and positional-value quotient/remainder.
5. The entrypoint bridge, relating the generated `sampler.add_small_base_p` result and its wrapped flag to that exact loop model.

The wrappers v1–v3 are retained as diagnostic failures; v3 first proved the entrypoint equality but carried an unnecessary second corollary that depended on an inaccessible private list-length helper. The green wrapper v3 source drops that redundant corollary and directly imports the retained `R1SamplerAddDigits` owner.

The Charon addendum records a runner metadata error separately from the underlying tool result: the runner failed to write a structured receipt with `KeyError: repository_revision`; GNU `time` records Charon exit status 0 and Aeneas consumed the resulting exact LLBC hash successfully. This is not relabelled as an ordinary successful Charon receipt.

No `.olean`, `.llbc`, executable, archive, or object file is included. Native object hashes and cache paths are recorded in the manifest/preflight evidence. Imported shared owners are pins only; their cache objects were not copied.

Publication check: `check-renamed-owner.py` verifies exact generated bodies under only the namespace rename and resource-option/comment removal. The three archived `.patch` files retain original blank/context whitespace; only those raw diff paths are excluded from the whitespace-style gate. Compiled sources and all other files pass it.
