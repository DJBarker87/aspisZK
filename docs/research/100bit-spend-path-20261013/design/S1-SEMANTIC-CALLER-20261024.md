# Same-call semantic roots and alpha through preparation and owned stage1

Target not yet established. S1 and S6 remain open. No Rust source, artifact,
security metric or cryptographic assumption changes in this packet.

## Enclosing statements changed

Previously the current preparation/owned-stage1 theorems retained a free op9
semantic verifier return. Static Prepared fields were tied to that value but
not to the semantic verifier's parser, transcript initialization, begin, finish
or root-copy operations.

`S1SemanticInstallationV1.install` replaces that release-None operation with the
complete retained verify_observed prefix and verify_finish bodies, transporting
the FULL public and semantic result/error carriers. Both carrier directions
are checked (`S1SemanticCarrierV1.semanticEquiv`), including all claims arrays,
challenges, points, transcript state/hash/cursor and all eleven default wire
error variants. A non-None observer still delegates to the original operation;
no claim about the legacy model's ignored non-None markers is made.

`S1PrepareSemanticRootsV1.prepare_semantic_roots` consumes one accepted complete
compact preparation under that installation. It derives the actual source
View, semantic parser call, same selected full public argument, public
transcript call, begin, finish, row-2 payload and conversion/unwrap calls. Both
returned Prepared roots are its parser C1 root and the exact bytes of that
row-2 payload. It also retains the SAME originalNew call, full returned scratch,
static semantic-alpha/point identities and canonicality of all ten semantic
alpha values. No independently successful semantic/prepare call, root identity,
chosen challenge array or alpha-canonicality premise is present.

`S1OwnedStage1SemanticRootsV1.owned_stage1_semantic_roots` composes this source
connection through the existing actual owned-stage1/first_decoded/tx1 bodies.
The full decoded statement, its semantic public argument and the original
public/proof/split arguments come from that one enclosing accepted execution.
The statement returns the reached originalNew call and post-preparation
continuation on the SAME Prepared/scratch and original checkpoint result.
It derives both root identities and all ten alpha word bounds there, with
release observer None. This is the owned source-model boundary, not an assertion
that the native SDK/account execution relation has been discharged.

`S1TopWriterSemanticV1.writer_semantic` connects the same root/alpha source
facts to the exact lead `VTop_Provenance.WriterPrefix` consumer. The full
source-body op7 installation and the reached writer execution are explicit.
There is no root-value, alpha-range, independent semantic execution or
preparation-success hypothesis. Existing writer variant/gamma/kappa/scratch
results remain applicable to that same installation.

## Reuse and compatibility

The prefix/finish model bodies and original complete finish/prefix proof spines
are reused. The new root projection follows the existing successful finish
spine verbatim and changes only its terminal projection; the generator checks
that relation. A concrete standard copy/unwrap installation derives the actual
row-2 bytes and conversion success. Canonical semantic alpha reuses
`SemanticRoundAlphaSelectedCanonical.verifier_round_alpha_canonical` on the
actual rounds return derived from finish; no round or sampler proof was redone.

The selected historical model objects initially referenced a Phase declaration
absent from the current selected public-preparation cache. Those objects were
not used as accepted finish/prefix results. The small prefix/finish model
modules were recompiled against an explicit alias of the complete retained
caller Phase carrier. No reduced phase token or new opaque type was introduced.
The old resource-option lines are removed from the recompiled finish model.

`tools/s1-semantic-port-20261024/check-models.py` verifies the exact model-body
and proof-spine reuse and selected native declarations. Twelve native function
bodies are byte-identical at a555c852664c80000942f0c911e16719a5493625,
b2727acd3abf79315d18b754a260f58f4b1c6326,
25866ec331cc7ce27dd9956609c11d32fa8fa58a and current research
7a40c5c2cf1135eb22f238418b802fd2d2f1fb40, and in this worktree. This includes
verify_observed, verify_finish, default semantic_rounds, public_transcript,
mark, Prefix parse/record/validated_record, begin and the validated semantic,
circle and block operations. This is a selected-declaration statement;
whole r1_wire.rs differs by feature-gated host/reference additions, and inline
attributes outside the selected declarations also differ. Complete files and
compiled artifacts are not claimed identical by this check.

## Exact remaining boundaries

Removing free op9 does not close the semantic component. Existing leaf
operations remain explicit: R.decode/boundary/value and B.fromFn/mask/add/mul/
terminal/circle/claims. Their concrete current-source instances must still be
installed. The root unwrap leaf is installed; accepted-only copy correctness
does not prove native panic formatting, allocation or abort traces. These are
source/runtime obligations, not extra cryptographic assumptions.

For the full lead PreparedBinding, root bytes must still be identified with
the stored compact proof's parsed commitments through the actual logical-buffer
expansion and parser/caller frames. Current preparation op10/op11 remain
unbound; this packet does not manufacture that identification from parser
success alone. The existing parser/multiproof cone's proved frames and codec
results should supply it. Circle output/source correspondence and the remaining
Prepared fields need their concrete source producers/backends. Actual full
transcript-prefix/state and ordered-read transport, native original claim/powers
association, SDK/account effects, S6 reconstructed-statement/input retention,
coherent dependency replay and final artifact re-pin remain open.

No S3/S9, S4 or S5 track is modified. The existing S9 circle-coordinate
canonicality proofs were located for reuse as the next point-producer input.
No candidate adoption is requested by these proof-only changes. Native adoption
or equivalence and affected-parent/release re-pin gates remain as specified by
S1-NEXT-FREEZE-HANDOFF-20261020.md and R22-TOTAL-20261021.md; default/devnet H5
authority remains f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 /
63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299.

## Validation

Source-only focused-extractor-proof-packet-v1 receipts, source/tool/import pins,
commands, exit status, wall time, RSS, swaps and printed axioms are recorded in
`evidence/s126-current-caller-20261021/s1-semantic-targets.json` and its listed
attempts. Every accepted target used the atomic local Lean lock and
`lake env lean -j1 -M4400`, with standard-only or empty printed axioms and zero
swaps. Only changed local targets and directly affected consumers were checked;
there was no unchanged full manifest replay. Thirteen accepted targets took
374.705361 seconds aggregate wall time, with maximum RSS 3,814,932,480 bytes,
zero swaps and 33 standard-only or empty axiom reports. Import hashes identify cached
objects without distributing binaries. Focused cached compilation is not a
coherent final release replay or actual frozen source/artifact closure.
