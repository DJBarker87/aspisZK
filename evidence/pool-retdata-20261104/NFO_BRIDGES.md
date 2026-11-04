# Pool return-data bridges

Status: qualified local evidence; the composed S2/S6/S10 join remains OPEN.
No NDT row, settlement root or headline is promoted by this packet.

## Frozen interfaces

The NFD ASR8 emission is 792 bytes. Its Pool consumer is
pair_forest_dispatch::invoke_pair_forest_terminal_with_runtime_v1, followed by
pair_forest::process_pair_forest_terminal_with_verifier_v1. The legacy
verifier_dispatch.rs ASVS decoder expects 384 bytes and cannot supply this join.
NFO_PoolReturnData.legacy_width_mismatch checks that mismatch. NFO_INSPECTION.md
pins the source, all three ELFs, successful-invoke/read instruction path, program
comparison and rejection branches. These are static findings, not an ELF replay.

## Native certificates and limits

All 60 native submissions are retained individually, including compile failures,
unwinding failures, positive checks and deliberately failing controls.

* K007: source-exact ASR8 read continuation after admission; clear/invoke/read
  order, same program check before length/decode, full decoder Result reply,
  exact decoder argument and saved bytes, full typed result via eight arbitrary
  field-family/coordinate observations. The success carrier has cap=len=792.
  This is a cut, not the full caller domain. K008–016 mutate the nine relevant
  checks/forwardings and fail; K040–047 separately corrupt all eight result
  projection families and fail. NFD_EmitProjection.complete supplies the reused
  mathematical extensionality law, not a new native result.
* K017: every returned length 0..1024 except792 is rejected before decoding;
  K018's reversed length assertion fails. K019/020 are passing/failing exact
  KMX copy controls.
* K021/022: ACTUAL frozen generic caller rejects wrong program / false acceptance
  control fails. K034/035 cover CPI error (nonzero syscall-coded u64 ProgramError),
  K036/037 absent reply, K038/039 wrong length. Decoder is poisoned and proved
  unreachable on these paths. These use ready account fixtures, initially
  xor-distinct keys, empty account data, arbitrary320-byte request; they do not
  prove all admitted account states or a PacketDomain.
* K054: source-exact ASR8 decoder cut on arbitrary792 raw bytes, with three
  local-record child oracles. It checks all header rejection branches, exact
  digest32/afterstate688/validator arguments, three call positions, full error
  propagation and all output field observations, plus immutable input frame.
  Digest error factory covers all seven AtomicStatementError variants. K025's
  earlier representative-error positive is superseded. K026–033 are the child
  argument/reply/error/frame mutation failures; K055 repeats digest-error
  mutation against the full seven-variant oracle and fails. Child bridges are
  the CLOSED slice-S decode_digest_canonical (NEQ), afterstate decoder (NEX),
  validate_result (NEQ/NBX), on arbitrary bytes/slices/raw result records. This
  packet does not turn this native cut into a proved accepted-codec inverse.
* K048: one KMX reallocation loop iteration on arbitrary pre-state with frame;
  K049/050 changed-byte/frame controls fail. K051: actual Box constructor value,
  returned allocation and freshness cuts; K052/053 controls fail. KMX_CopyMeaning
  supplies the existing value/frame/induction laws. A full allocator/Vec ABI
  transport or whole-buffer proof is not claimed.
* K056: FAILED full-caller CPI argument experiment with independent account keys
  satisfying the explicit admission constraints and any of three loaders. The
  meta pubkey/readonly conjunction and AccountInfo key association assertions
  fail. Cause unisolated; no shipped bug, no metadata fidelity credit. Do not
  treat K059 as its repair. K057/058 isolate AccountMeta::new_readonly key/signer/
  readonly constructor observations with matched key corruption. K059/060 check
  the same broader caller's request pointer, length320, observed byte, selected
  program and account counts / false request-byte control. These pass/fail as
  expected but leave K056's account associations OPEN.

Every run selects the deployed Pool aggregate features
r1-split-checkpoint,pair-forest-source-invariant-audit,
pair-forest-source-result-invariant-audit. Each records resolved features for
EVERY crate, graph equality to the frozen lock (including cfg-if/libc), offline
mode, and unchanged lock after the run. No unsupported --locked Kani flag.
Exact KMX patch sha256:
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
All oracles/logs are local records. No writable static, Option<fn>, field
multiplication, SHA, proof_for_contract or stub_verified is used. Suspended
static/function-pointer harnesses: NONE. No field-multiplication stub table is
needed. No LPb passing stage is imported or credited.

K001 was an own missing alloc hook; K002 an insufficient frontier-factory unwind;
K003 a whole-record memcmp shape, split into arbitrary field observations.
K004 is superseded; K005 accidentally repeats it after own preparation validation
failed before changing source, receives no extra credit. K006 fails an overstrong
pointer/value conjunction on a larger-capacity Vec: into_boxed_slice may shrink
and reallocate. No individual conjunct was isolated. SDK static cap=len evidence
and later KMX/Box cuts support a route, not closure of this generalized carrier.
K023/024 were own helper-extraction/signature errors. No timeout or memory kill
occurred; no timeout/resource cap was raised.

## Lean and extraction

E001 uses the NCO Charon/Aeneas pins on the actual frozen decoder wrapper, in an
optimized offline reference build. Raw outputs and LLBC are pinned once. Its
external template (19 axiom declarations) is TEXT ONLY, never compiled/imported.
NFO_RawDecode adapts just the emitted decoder body/closures onto the coherent
canonical carrier/child owners; NFO_DECODE_ADAPTATION.json records every change.
The reference crate has its own pruned dependency lock, separately checked as
such; it is not the frozen Kani scratch lock. No new top decoder owner is silently
adopted. No XRn_Join or stand-in is used.

Checked supporting facts: arbitrary-result serializer layout and injectivity,
afterstate injectivity, scalar/u64 roundtrips, fixed-width flatten injectivity,
child error maps, raw wrong-length rejection, oracle substitution, packet success
inversion. NFO_Final.codec_iff_raw precisely reduces the OPEN AcceptedCodec to a
raw792 accepted-inverse; it does not prove it.

NFO_PoolReturnData.association composes JHb_Emit's accepted emission with the
model read under RuntimeReturnData and explicit OPEN DecoderAssociation.
NFO_AcceptedAssociation.consumed instead assumes an accepted Pool model read and
OPEN AcceptedCodec, then derives the SAME emitted typed value, saved bytes and
Pool-local clear/invoke/read/decode markers on the SAME context parameter.
Markers are local runtime call order, not equality of the entire inherited CPI,
query, settlement or oracle history. Complete native same-context/settlement
correspondence is separately OPEN. The deployed settlement consumes value() and
re-encodes; its exact_bytes shortcut is feature OFF.

All new proof modules compile using only standard axioms. The final hardened
raw audit has eight successful planted fixtures, only standard axioms on all29
roots, but five raw/collectAxioms mismatches: aggregate audit FAILS. See
NFO_AUDIT.json; do not present this as a complete ax2 pass. NFO_RUNTIME_SCOPE.md
records the SDK empty-return-data incompatibility and cap/length limitation.
