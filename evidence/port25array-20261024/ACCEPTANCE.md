# Port25ARRAY concrete acceptance criteria

Base dcf419f291d43299ddca4482bef469cbd8ff8f04; branch codex/cx-port23push-20261024.
Port23 remains UNMERGED/UNADOPTED. No shipped/backend/raw extraction/template,
trust, protocol, feature, security-contract, key, RPC or chain changes.

1. Literal pinned native array IntoIterator delegates `self.iter_mut()`;
   compose the existing array-to-slice mutable wrapper, Slice.iter_mut and
   IterMut content interpretation. The caller-required back ABI consumes
   an IterMut transformer. Preserve the complete array carrier and prove
   the back composition law. The rejected value ABI remains evidence.
   A chosen interpretation alone does not prove its native association;
   explicitly separate source delegation, approved content semantics and any
   remaining source-refinement gap. No unsafe/panic/allocator expansion.
2. Prove symbolic lane/order facts before specializing the actual source
   add-all-then-fold loops to four lanes and joining S7 per-lane add/fold.
   Quantify arbitrary full U32/U64 words, raw Vec, terms, index and four-word
   power. Include all Result outcomes, bounds and overflow. Do not assume
   canonicality, a safe domain or the desired equality. If the unrestricted
   equality fails, retain the counterexample and stop that claim.
3. Only after the actual row equality, compose the concrete complete Vec
   frame. Query effects need a separate fixed primitive interpretation and
   ordered rejected-prefix association; Result/carrier equality proves none.
   Retain op6/four_dots/geometry/line/circle/accumulator/trace/observer gaps.
   Port17 reached release None is not a Some-to-None retargeting license.

Budget: at most seven additional Lean invocations, charged to original Port23
13 ceiling (six used). Kani/Rust/extraction/backend/ELF/full-manifest zero.
Use the pinned warm local j1/M4400 path, shared atomic lock and aggregate 8GiB
guard; no cold build or other owner modifications. Smallest new lemma, actual
row bridge, then one full statement/axiom audit; preserve failures. Each new
receipt includes exact command, exit/wall/RSS/swap, revision, source/import
object/tool/sysroot hashes and pre/go/post checks; no binaries/objects.
Both security targets remain not yet established. No final manifest authorized.
