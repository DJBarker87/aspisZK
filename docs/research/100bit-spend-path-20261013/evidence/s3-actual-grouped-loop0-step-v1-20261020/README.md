# S3 grouped inactive-pair, actual generated loop 0 step

This packet records a source-cut extraction of the frozen private helper
`s2_grouped_inactive_pair` and focused Lean proofs for its actual generated
loop-0 body, the concrete `field`/addition operations adapter, and the actual
group-index bound. It does not prove the whole helper or establish that its
input bytes decode successfully. `decodeField` success remains an explicit
premise for the loop-body theorem; the complete helper prefix/loop proof and
connection to validated production input remain open.

The source revision is `8137980396719c48f71f743254644aaf0a3a8423`. Exact full
Rust files are included under `sources/rust-upstream/`. The extraction input
shim is preserved byte-for-byte under `sources/extraction-v5/input/`. It
copies the actual eight-U32-limb carrier (`WideExact` is two `QM31` values,
each `QM31` is two `CM31`, each `CM31` is two `M31`) and the corresponding
zero constants, and retains the helper body over `f: &[u8]` with its actual
`field(f, j)` call. The helper visibility is promoted from private to public
solely to select the extraction root. The byte checker verifies this exact
transformation and the copied carrier shapes.

The v5 Charon/Aeneas receipts are preserved unchanged. A provenance defect in
the original `input/source-pins.json` was discovered during packet review:
its `candidate_transform` describes an unrelated powers rewrite, and its
`source_cut.function_sha256` / public function text do not match the private
upstream span. The original receipt records the hash of that stale sidecar.
This packet does not rewrite the receipt or treat that sidecar as a valid
source pin. Instead, `corrected-source-pins.json` binds the included frozen
Rust files, exact private function span, extraction shim, commands, LLBC,
translation metadata, and generated source. `provenance-correction.json`
records both the mismatch and the independent checks. `check_source_cut.py`
recomputes the relationships from the included bytes.

The extraction Cargo package retains the label `aspis-r1-current-powers` from
the reused minimal kit. The command runs Cargo from the recorded `input/`
working directory, and the LLBC/Aeneas metadata records that same package
name and the selected grouped-pair function. This is a minimal source-cut
crate, not a whole-crate extraction. The opaque cuts are exactly the byte
field decoder and `WideExact.add` / `WideExact.mul`.

The Lean generated-owner adaptation is also checked byte-for-byte by
`check_source_cut.py`: it strips the generated resource-option overrides,
removes the external-template import, renames the namespace, introduces an
explicit `Operations` record, and threads its decode/add/mul fields through
the generated bodies and callers. No template axiom owner is imported. The
adapted owner has no heartbeat or recursion-depth option overrides. Lean
receipts list standard axioms only: `propext`, `Classical.choice`, and
`Quot.sound`.

No `.olean`, executable, or archive is included. Object hashes and native
cache paths are recorded as evidence metadata only. The older U8 dummy-carrier
v3 extraction and the mistaken local same-named stale-powers directory are
rejected diagnostics; neither supplies a source, object, or receipt in this
packet.


The rejected paths and reasons are enumerated in `diagnostics/rejected-provenance.json`. The selected recovered path is distinct from the stale same-named local directory.
