# J1.R4 cut, view, salt, and length reuse inventory

Read-only mapping of the remaining J1.R4 items in
[`LEAD-REVIEW-J1-20261015.md`](LEAD-REVIEW-J1-20261015.md) to existing Lean
interfaces. This note records checked model facts and missing connections; it
does not decide the required source correspondence or security premises.

## Commitment cut and view maps

The generic causal table cut is already proved. In
[`../lean/FirstReadCut.lean`](../lean/FirstReadCut.lean),
`AspisR1.FirstReadCut.first_read_cut` decomposes any trace containing address
`a` as `pre ++ (a,value)::post`, with `a` absent from the earlier prefix;
`tableBefore_representation` identifies the table at that first occurrence
with `TraceTable.replay` of `pre`. The underlying
[`../lean/TraceTable.lean`](../lean/TraceTable.lean) theorem
`AspisR1.TraceTable.tableBefore_cut` supplies this equality when the cut
position and absence-from-prefix fact are explicit.

Commitment recovery is stable under that cut. In
[`../lean/CanonicalTableRecovery.lean`](../lean/CanonicalTableRecovery.lean),
`CanonicalTableRecovery.recover_eq_of_replay_eq` says `recoverAt` has equal
results for two replay-equivalent logs under consistency, read inclusion,
first-read budget, and the existing collision exclusion. Its
`represented_before_cut` specializes this to a represented log that replays
to the table immediately before the first occurrence of an address. The
concrete C1 adapters are
`C1TableStability.c1_table_word_stable` and
`C1TableStability.c1_table_word_of_read` in
[`../lean/C1TableStability.lean`](../lean/C1TableStability.lean): the former
compares recovery at the C1 initialization frame between a represented log
and the full trace; the latter obtains the cut from `FirstReadCut` given a
read. These conclusions are for `recoverAt 0x71 480` and the stated finite
table/recovery model.

The transcript-facing view maps are also present. `UnifiedRun.transcript`
and its `transcript_statement`, `transcript_length`, `transcript_rounds`,
and `state_succ` lemmas give deterministic prefix bookkeeping. In
[`../lean/UnifiedSemanticActualView.lean`](../lean/UnifiedSemanticActualView.lean),
`UnifiedSemanticActualView.actual_output` identifies `UnifiedSemanticDecoder.view`
with the deterministic run at rows `1 ≤ n < 26`, assuming the row-zero label
and encoding equalities. In
[`../lean/UnifiedOpeningView.lean`](../lean/UnifiedOpeningView.lean),
`UnifiedOpeningView.actual_output` gives the corresponding representation
equality at rows `27+k`, `k<4`. These are generic-model view equalities, not
proofs that a source parser returns the view inputs.

The before-row parser bridges are explicit. In
[`../lean/UnifiedSemanticRecovery.lean`](../lean/UnifiedSemanticRecovery.lean),
`UnifiedSemanticRecovery.typed_before_row` proves that the 27-fuel semantic
walk and raw-record decoder return the expected prefix records at the table
before row `n` for `0<n≤26`. It assumes a consistent prior trace, public
length bound, row-zero label/encoding equalities, first-read bound, and the
existing bad-collision exclusion. In
[`../lean/UnifiedOpeningRecovery.lean`](../lean/UnifiedOpeningRecovery.lean),
`UnifiedOpeningRecovery.recover_before_row` handles the table before row
`27+k`, `k≤4`; it additionally requires the existing tail-state collision
exclusion and returns the typed semantic-plus-opening prefix together with
known-cell and read facts. `TypedPrefixExtension.semantic_typed_append_eq`
and `.opening_typed_append_eq` prove that these typed parser results are
unchanged when a suffix is appended, provided the cut address already occurs
in the prefix. This is a first-read-cut equality, not an unconditional
invariance claim for arbitrary addresses.

The typed-row-to-old-view adapter is now present in
[`../lean/SemanticPayloadOpeningView.lean`](../lean/SemanticPayloadOpeningView.lean):
`SemanticPayloadOpeningView.opening_view_of_payloads` calls the reused
`MaskView.openingViewZ_of_parsed`. It takes the typed context, row-indexed
`RowPayload`, challenges, explicit `recoverC2` callback, C2-base condition,
circle messages/points, and point side conditions as inputs. It does not
derive those inputs from a current source parse or accepted unified run. The
earlier inventory
[`J1-PROTOCOL-VIEW-REUSE-20261015.md`](J1-PROTOCOL-VIEW-REUSE-20261015.md)
records the old parser's downstream requirements. Typed C2 word plumbing is
also available: `TypedRecoveryContext.c2Words_full` and `.c2Base_full` build
the existing `TypedContext` interface from the typed word model, while
`RecoveredC2Semantic.pair_c2Words` and `.pair_c2Base` transport a decoded C2
pair into it. At an accepted C2 opening,
`CanonicalC2SemanticOpening.c2_pair_at_of_no_events` composes
`CanonicalTypedOpening.c2_decode_of_no_events` with the recovered-pair
projection and proves both indexed coordinates equal the decoded payload
coordinates. Its trace consistency, commitment-read, accepted Merkle path,
opening-read containment, first-read budget, and three no-collision premises
remain inputs. This still does not derive the `recoverC2` callback over all
states or row payloads expected by `opening_view_of_payloads`, nor does it
prove that a source parser supplies the typed rows and circle-view premises.

For record extension, `RawRoundDecode.decode_append_one` and
`RawRoundAppend.decode_append` give structural list-decoder composition;
`TraceAppend.tableBefore_append` preserves a before-table under an appended
trace suffix when the address was already read in the prefix. The two
`TypedPrefixExtension` theorems apply that identity directly to the semantic
and opening typed parsers, so callers can reuse the exact parse result across
such a suffix extension.

## Selected typed bridges and remaining adapters (HEAD `daa96e811d70`)

[`../lean/SelectedTranscriptParams.lean`](../lean/SelectedTranscriptParams.lean)
adds `SelectedTranscriptParams.params` with `L=131072`, `D=3717`, 33 rounds,
zero IV, `SelectedChallengeMap.sigma`, and an identity byte codec on the
subtype of messages whose lengths are at most 3717. Its
`publicStatement` constructor takes `bytes`, a public value, and a proof that
`SemanticPublicWire.parsePublic bytes = some pub`; it derives the model's
`initFits` from `SemanticPublicCodecComplete.parsed_init_fits`. This is a
bounded raw-message parameterization: row-specific message validity is not
encoded in that subtype.

The current typed recovery chain also includes
`TypedRecoveryStability.typed_word_stable`, which compares total typed words
built from separate represented C1 and C2 first-read tables with the full
trace's words, under the two component stability premises. The accepted
opening interfaces are `CanonicalTypedOpening.c1_decode_of_no_events`,
`.c2_decode_of_no_events`, and `.folded_decode_of_no_events`; each retains
its supplied six-level path and explicit read, consistency, budget, and
no-collision conditions. `CanonicalC2SemanticOpening.c2_pair_at_of_no_events`
then returns the two C2 coordinates at an indexed query from the successful
C2 leaf decode. These are typed model bridges; they do not determine paths
from the source transcript or prove a source parser connection.

Rows 25 and 26 need their row-specific circle conversion kept visible.
`SelectedChallengeMap.sigma` returns `semChal` on those rows, and
`.circle_parameter_rows` shows that `rhoOf` extracts the `qm31Sample` circle
parameter. `.first_circle_view` and `.second_circle_view` then apply the old
`circleSampleParameter0` and `circleSampleParameter1` maps to obtain
`circleSample0` and `circleSample1`. Those maps preserve their nonzero
imaginary-part accepted branch and fallback behavior. The old
`UnifiedEventDensity.classifier` still returns `False` when the prefix length
is 25 or 26; these selected challenge-view lemmas do not add classifier or
density coverage for those lengths.

The selected byte-to-payload parser layer is now present as model plumbing:
`SelectedIndexedRead.readTyped` combines the indexed message label/encoding
check with a supplied row decoder; `readTyped_sound` and the encoded-read
lemmas characterize that wrapper. `SelectedSemanticRead.read` sequences the
25 dependent semantic-row decoders at indices 0--24 and provides
`read_eq_some_iff` and `read_append_stable`. `SelectedOpeningRead.read`
reads rows 25--31 (two circle payloads followed by gamma, kappa, first,
second, and final opening payloads) and provides the corresponding exact-read
characterization and prefix stability. `SelectedTranscriptRead.read` combines
those results with the row-32 rho decoder. Its `readExact` additionally
requires `rs.length = 33`; its theorem `readExact_eq_some_iff` states exactly
that length condition plus all `Reads` facts. The separate `read_append_stable`
lemmas are conditional: they preserve parsing only when every required index
is already inside the original record list (`24 < length` for semantic rows,
`31 < length` for opening rows, and `32 < length` for all 33 rows). Thus
prefix-stable reads do not imply successful reads from a shorter prefix.

The raw/typed record boundary now has an explicit canonicality route. The
generic `RawRoundCanonical.encode_of_decode` requires the premise that every
successful `p.dec` re-encodes to the same bytes; this is stronger than the
generic `decEnc` field by itself. `SelectedRawCanonical.dec_sound` proves that
premise for the selected bounded-message codec, and
`SelectedRawCanonical.encode_of_decode` specializes the generic list theorem.
`SelectedTypedReads.semantic_eq_raw_of_decode`, `.opening_eq_raw_of_decode`,
and `.transcript_eq_raw_of_decode` then show that the selected readers run on
an encoded typed `Rec` list exactly as they run on the original raw list,
provided that raw list successfully decodes to those records. These theorems
preserve all five raw record fields; the tuple layout is
`(prev, absorbed, message, next)`, while `RawRec` separately stores
`(prev, absorbed, label, data, next)`.

`SelectedInitialRecord.row0_message_bytes` identifies the selected typed
row-zero message bytes with `PublicInitFrame.emptyRecord`, and
`.params_message_bound` establishes the selected message bound is at least
the empty-record length. This is a byte-model connection for the initial
record, not a caller/source parser result.

There is also a separate challenge-bearing-prefix view. `SelectedSemanticPrefix.read`
consumes `List (Message × E)` at a supplied starting offset, decodes semantic
rows 0–24, and retains each supplied challenge. Its `read_length` and
`read_append` establish successful-length preservation and exact append
composition. `SelectedSemanticPrefixFacts.read_challenges` proves that the
parser preserves the input challenge list; `.semChalsZ_lift` reuses the old
`R0P.Mask.semChalsZ_of_pairs`, and `.semChalsZ_read` composes the two. These
facts do not construct those challenge-bearing pairs from `Rec` records or
prove the pair challenges equal the selected `p.σ` values.

For challenge-timed opening reads, `SelectedOpeningStages` defines nested
`Gamma`, `Kappa`, `First`, and `Second` stages. They read rows 25–27, then
row 28, row 29, and row 30 respectively; each append-stability theorem is
conditional on that stage's last row already lying in the original prefix.
These stages intentionally stop before later payloads and carry no challenge
or recovered-word fields. The full `SelectedOpeningRead` remains the separate
parser for rows 25–31, and `SelectedTranscriptRead` for all 33 rows.

The parsed opening payloads also have an existing algebraic interface.
`SelectedOpeningClaims.Y` and `.parts` arrange six 29-entry vectors from the
row-25, row-26, and gamma payloads. `SelectedOpeningData.Payloads` packages
rows 25--31, and `SelectedOpeningData.data` inserts those payload-derived
claims/polynomials together with explicitly supplied `W`, `V`, functionals,
and challenges into `MatchingSupport.Data`. `SelectedOpeningPairing.acceptedPairing_iff_coefficientChecks`
rewrites the existing accepted-pairing predicate as the three coefficient
checks on the parsed payloads. These constructors consume supplied parsed
payloads and model inputs; they do not establish that an accepted unified
run supplies them.

Relevant current source pins at this inspection are:

| Module | Source SHA-256 | Status note |
|---|---|---|
| `SelectedIndexedRead.lean` | `0c44871e4c84fc545381a6df9bb2d8fa23102f4d2af229da2b6600fa56003b35` | indexed label and decoder wrappers |
| `SelectedPrefixRead.lean` | `6ecff471af039433f7ffe7103db006dc10c847b309ec3756c4c10bbb9eb02dab` | indexed reads and append stability |
| `SelectedSemanticRead.lean` | `ac332f97ddbcb98feaf6d4df30f54995fcec4e430ccb374f07d1afafc1d0eb59` | 25 dependent row decoders |
| `SelectedOpeningRead.lean` | `9a0f72a9e447f1d87a625dec7fc0cdffdd8093f91e7dae2cee3ecec534cc7dcc` | rows 25--31; focused attempt b green (source SHA recorded above) |
| `SelectedTranscriptRead.lean` | `11bcce167ce868f86692d0fe654f6066187bd1da4c0714f6a3165036dbc80557` | all 33 rows and exact-length wrapper |
| `SelectedOpeningClaims.lean` | `e219644ff5ac0049f4a153c8d228bccafc4d4722d23a06bdbf8dfb722710864c` | six-vector/parts model |
| `SelectedOpeningData.lean` | `035c7d6b52c7eb80f250414ed68e9711b0dd88e35a04247fa95dab55a2b4a824` | payload-to-`MatchingSupport.Data` packaging |
| `SelectedOpeningPairing.lean` | `bf227c7e561bd3ef66c537f0769565f365d6abff3aaff93aa71c62b3369c1c7c` | accepted-pairing coefficient equivalence |
| `RawRoundCanonical.lean` | `6eba5fad8a8916e9f2418a863a04e192bff1cc4ed3267cfc4b507b581cd107d8` | generic raw-list inverse under explicit decoder canonicality |
| `SelectedRawCanonical.lean` | `f84ea3ad25ff6d037eb13b6cb823fdf00cc524073ef6e60292a8d52d1823f458` | selected bounded codec canonicality and specialization |
| `SelectedTypedReads.lean` | `6536c236e8842e265d0442b8ae3d9aacedd4c9cec204ca035ca59e0a0a17a5f4` | raw/typed selected-reader equality and typed append stability |
| `SelectedInitialRecord.lean` | `5bbe262f678158f9d8831626720de293438f606c1be8c23782e16c98ef7c0a52` | typed row-zero message equals the modeled empty record |
| `SelectedSemanticPrefix.lean` | `1c465621c5924f3d0b275ad151b141329a3e541aee4d22c3a831b35451fd22e9` | challenge-bearing semantic-prefix parser, length and append laws |
| `SelectedSemanticPrefixFacts.lean` | `733444507012726a2d29b8b087f6c21f37ba4a96bb94aef87f51e7776d21004b` | challenge preservation and `semChalsZ` adapter |
| `SelectedOpeningStages.lean` | `c87ad5c67f3c57fbc37dc8394a390a8e45c6a6a638c8cae7d0839af4245c1786` | gamma/kappa/first/second indexed row stages |

The raw/typed round trip does not by itself identify a state-derived
challenge-bearing input sequence, nor does the staged opening parser provide
the words or callback expected by the old view. Remaining interfaces are:
(1) connect these model reads to the actual selected
source transcript/caller and its challenge values, including the source-level
row labels and serializer; (2) derive the `payloads`, challenge list, and
`recoverC2` callback consumed by `SemanticPayloadOpeningView.opening_view_of_payloads`
from a source-backed accepted run; (3) derive its C2-base, point distinctness,
and non-rationality premises from that execution; and (4) prove the relevant
source/caller and classifier interfaces. The byte-model parser itself is no
longer absent, but no source refinement or J1/security conclusion follows from
these parser theorems. This inventory does not select premises or claim those
remaining interfaces are closed.

## S2, private salts, and row challenge maps

At the generic FS level, `FS2.Duplex.Params` in
[`../../v8-fs-generic-20261006/lean/FS2/Duplex.lean`](../../v8-fs-generic-20261006/lean/FS2/Duplex.lean)
contains `lbl : Nat → Byte`, `σ : Nat → State → Cv`, `enc`, `dec`,
`encLen`, and `iv`. `σ` is an unconstrained challenge function at this
interface; it does not encode source profile or salt selection by itself.
The unified sampler fixes the row schedule only (`roundCount = 33`): row 0
uses `PublicInitFrame.row0`, row 26 uses `OpeningReseedFrame`, row 31 uses
`QuerySamplerBridge`, and ordinary rows use `DuplexSamplers.plain`.
`UnifiedSampler.row_zero`, `row_reseed`, `row_query`, `row_ordinary`, and
`row_rho` are definitional schedule lemmas. They do not pin the caller's
`lbl`, `σ`, `enc`, or `iv` to a Rust profile.

The existing challenge-law assumptions are explicit and reusable:

- `UnifiedSemanticDensity.semantic_density_bound` requires
  `hsigma : ∀ i, i < 25 → ∀ s, p.σ i s = semChal s`.
- `UnifiedEventDensity.density_bound` carries that semantic assumption,
  separate row-27 gamma-sampler equality, rows 28–30 sampler equalities,
  and a row-32 reduced sampler equality. These are the exact identities used
  by the old per-row density results.
- `UnifiedSampler.unified_law` proves the generic independent-answer law for
  a valid row when `i ≠ 31`; row 31 has its separate query law.

Those APIs consume identities as premises; they do not derive the concrete
R1 row maps from a source seed/salt configuration. The byte-model domain
constants are already explicit. `PublicInitFrame.domain` is the fixed byte
list for ASCII `UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3`; `pre pubBytes` is
`domain ++ [0] ++ lengthBytes pubBytes.length ++ pubBytes`, and `addr_bytes`
appends `bytes c1`. `lengthBytes` emits four little-endian base-256 bytes.
`frame_length` proves `75 + pubBytes.length`, and `addr_bytes` exposes the
complete modeled input. Thus the model pins the P3 initialization-domain
literal. `RowZeroCodec.row0_absorb` separately identifies row zero with the
generic `absorbA` only under `p.lbl 0 = 160` and
`p.enc m0 = PublicInitFrame.emptyRecord`; those assumptions are explicit.
The relationship to the feature-selected Rust `DOMAIN`, the call's checked
`u32` conversion, and the exact source `HashFn` invocation remains a separate
correspondence proof; `PublicInitParse.parse` additionally takes
`pubBytes.length < 2^32`.

`OpeningReseedFrame.domain` is likewise fixed to the P3 opening-domain bytes
for ASCII `UNPROVED:R1:PRIVATE-SALTED:P3`; its `frame`/`addr_bytes` model
`domain ++ [tag] ++ bytes state`, and `frame_length` proves 62 bytes. This has
the byte-tuple shape hashed by Rust `Transcript::new` under the
`private-leaf-salts` feature (`domain`, `variant.tag()`, semantic state), but
the Lean `tag` is a free byte and there is no theorem mapping it to
`Variant.tag()`, the model state to the source transcript state, or the
abstract oracle `H` to that Rust hash call.

The source `r1_wire.rs`/`semantic_wire.rs` choose
`DOMAIN = b"UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3"` with the
`private-leaf-salts` feature and a different legacy domain without it. The
textual match to `PublicInitFrame.domain` is established by inspection of
these literals, but no theorem connects Cargo feature selection to that model
constant or source transcript initialization to `H (PublicInitFrame.addr ...)`.
Rust `SemanticTranscript::sample_block` carries out absorb/squeeze/advance;
the Lean maps remain generic transitions around an abstract hash model.

Private Merkle leaf salts are separate from both transcript-domain uses.
`prover.rs::derive_private_salts` asks the reserved attempt to derive each
leaf salt under a tree tag. The entropy implementation hashes a leaf-salt
domain, attempt binding, mask nonce, tree tag, leaf index, and salt seed.
Neither entropy context nor these derived values are fields of generic Lean
`Params`, and there is no Lean source mapping for them. Finally,
`VERSION_V4_S2` selects the v4, two-sample-per-fold proof envelope. That is a
separate selector: its presence alone does not establish that generic Lean
`Params` match the P3 feature branch or S2 source sampler.

## Length and framing bounds

Several bounds are already explicit, but at distinct boundaries:

- `UnifiedSampler.Public.initFits : 75 + pubBytes.length ≤ L` makes the
  public initialization address constructible. The decoder-side
  `PublicInitParse` APIs additionally take `pubBytes.length < 2^32` for the
  four-byte public-length frame; `UnifiedSemanticRecovery.typed_before_row`
  takes this as `hpub`.
- `Params.encLen m : (enc m).length ≤ D` and `Params.hL : 34 + D ≤ L`
  bound generic message absorbs. `UnifiedPrefixedReads` and recovery proofs
  use `p.encLen` directly. `UnifiedSemanticRecovery.typed_before_row`
  derives the read and state-transition facts from those generic bounds.
- `SemanticRecordCodec` fixes modeled payload sizes by row: 0 bytes for
  empty rows, 32 bytes for C2 root and mask sum, and 896 bytes for the
  28-coefficient polynomial. `RecordFrameCodec` provides exact frame length,
  exact header matching, and `parse_sound`/round-trip lemmas. These are
  Lean byte-model results; the frame-codec inventory explicitly leaves
  Rust u32 parsing correspondence separate.
- `Merkle32Leaf.leaf_input_length` and `CanonicalMerkleProgram.fullTrace_bounded`
  bound leaf/node oracle inputs for the commitment-recovery model. They do
  not supply a bound for the source `σ` map, which takes a fixed-size
  `State` and returns a challenge value.

No theorem gives a single end-to-end length statement for the selected
source version's public serializer, feature-selected parameters, absorbed
typed payloads, and challenge-row maps. The mathematical parameterization
and public byte parser now exist, but their connection to source execution is
not proved. Remaining interfaces include: (1) source/profile-to-parameter
mapping and Rust public-parser refinement; (2) the row-specific message
parser and payload/callback construction described above; and (3) a length
bridge discharging generic bounds from the selected source encoding. This is
an inventory of interfaces, not a proposal to change any theorem's premises.

## Inspected source pins

The original inventory below was recorded at HEAD
`136b746805f3438507732622c9b4e50f36bf49f9`; it is historical, not the
current bridge source pin. Current bridge files were checked at HEAD
`764bf20a6fe0392951b670f73748a54f70c9f272`:

| Current bridge | SHA-256 |
|---|---|
| `lean/SelectedTranscriptParams.lean` | `489f8b49c6a102f85c511ad4f4907dbeca479322b7184a563eda8c4a17c2dce0` |
| `lean/SelectedChallengeMap.lean` | `36bcd2bb277dcb2b34564656c71ebb7b14742c584ce931328a2ad1dbe03e5aad` |
| `lean/TypedPrefixExtension.lean` | `80ec6b3e680e4b0c48b0d732e2afd89deaeb7b68d909c6600e6ada55c7bcd4a3` |
| `lean/UnifiedSemanticRecovery.lean` | `971f84897f0c546fdd6488e197bc887062fb3904a4e520dc6595ada317a14d88` |
| `lean/UnifiedOpeningRecovery.lean` | `8f1d6602dc28f221d689746cd03d7b2be97679b5468455295f3edabede2736d5` |
| `lean/SemanticPayloadOpeningView.lean` | `bb3a10730f44cd10abeb0e581a818365963512841a4e4d7b4be6542760d57454` |
| `lean/TypedRecoveryContext.lean` | `2996554b29c722580cb6f105015803bbb1ac1f0847532f6aef32366e1496f0bb` |
| `lean/TypedRecoveryStability.lean` | `1ae695c97a097610d6a22da8ec83f4f6c566377297e5298851d6ef74a1150754` |
| `lean/CanonicalTypedOpening.lean` | `0a045246dff9119b10c450ac6debcbce79bea3a866042d53ed5efe1e9b1d8543` |
| `lean/CanonicalC2SemanticOpening.lean` | `1edd0299dc9914dd2e862441ab0ad744f5ce6734623c70e8e88732550be11fac` |
| `lean/UnifiedEventDensity.lean` | `b552274d799b3b192daafee66287c74496699304e72ec89a2159f276a3b5da89` |

The original inventory pins follow.

| File | SHA-256 |
|---|---|
| `design/LEAD-REVIEW-J1-20261015.md` | `07b1e6e8a2d7129c520b897d030a0810eccf5fd5ebd19926858bd9eddef9ff25` |
| `design/J1-PROTOCOL-VIEW-REUSE-20261015.md` | `2706d1ccdffec6520d296d8e20da12b44dbcaea56de722db6e45be0e0618d272` |
| `lean/FirstReadCut.lean` | `ba8b98c84f9d9168850005fab77dd656a525dbf0ed52781ca97620055943a31e` |
| `lean/CanonicalTableRecovery.lean` | `7e62ac6515d0a21addbbf213323e80a6265e8747e4a6a61e89174ffea0e3e5ee` |
| `lean/C1TableStability.lean` | `be8c0856d229f363a852922af3394841bfcbb19e289c08e6a4f4436ba9b8e36f` |
| `lean/SemanticPayloadView.lean` | `63d8ee366a6ca1beb5c4de26110419ddcaf83f87efb8de9d3151e24c0ef6506b` |
| `lean/SemanticRecordCodec.lean` | `5cf8fb6510c397d5d3c505b72bc24a5b2f4079ccb5a9e74e0c2eed14229bcbd3` |
| `lean/UnifiedSampler.lean` | `ac0ed518595233c81a4b2c3f368bb20c513cb29b888f19dc586801a9ac0b98ad` |
| `lean/UnifiedRun.lean` | `473377ddd83cf309745e1cad9ad9edc96cc256e70a9d4467144d15f80cc2b259` |
| `lean/UnifiedSteps.lean` | `c770459d19ccb3f916f27471b470bdf4c7e8c9c73666b97341a47c62d2e97f2f` |
| `lean/UnifiedSemanticActualView.lean` | `3ae47f0dcaf56385c9f9eb705364157b952e0a954b6dba27aa8d555d4ad37d8f` |
| `lean/UnifiedOpeningView.lean` | `6b7930f94d7f48189162f58f9ccf3eedb165e56d3d3e50b93ac0cd09808e735f` |
| `lean/UnifiedSemanticRecovery.lean` | `971f84897f0c546fdd6488e197bc887062fb3904a4e520dc6595ada317a14d88` |
| `lean/UnifiedOpeningRecovery.lean` | `8f1d6602dc28f221d689746cd03d7b2be97679b5468455295f3edabede2736d5` |
| `lean/PublicInitFrame.lean` | `756b529e3685c3341064b9970f5cebe71991b67eeeb5c6476a93934359f9a65e` |
| `lean/OpeningReseedFrame.lean` | `6624eb83586e4fff4b6e0f6686936baea1dca839c8174d81012bb64fc5fa032f` |
| `lean/TrailingStateFrame.lean` | `ebe717b3076421cc3f83b90a454c18bf1619f320feb65bc901aa3cb11c0e1711` |
| `lean/PublicInitParse.lean` | `cd7137ec47e4374dc3e776ab01638b12cc7a842920a38980f6fccdb9dbdf775a` |
| `lean/RowZeroCodec.lean` | `0ba6b54585a6fccc51f45a0993c596d1cf627d29c001c279ff8f5a1f00a344ea` |
| `lean/DuplexSamplers.lean` | `6ae5ba2277f2881deb909fa60667dab008be0a02b2d55f9ec5c20f698fa5e4a3` |
| `lean/UnifiedEventDensity.lean` | `b552274d799b3b192daafee66287c74496699304e72ec89a2159f276a3b5da89` |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/transcript.rs` | `c91ffe824a55ff62659e8a194d2ea201032383e4e11e5f60625404a30c691ef6` |
| `crates/aspis-r1-cost-probe/src/prover.rs` | `a7e20e5eb2fb706f2bdb51371466d4ee02c6fcabc67a427495a3b9276d9495fd` |
| `crates/aspis-prover/src/state_only_entropy.rs` | `78ebbb3176daf23935243452992548ff9d877aaaf853d73e5ee46b60d8cb3ec0` |
| `crates/aspis-core/src/proof.rs` | `a8e3b259da25d47a3d88b38ca838d57ab104476929fe5758b43d1a37c06306a0` |
| `lean/UnifiedSemanticDensity.lean` | `db2457d02da3ce58cec52092eab5cfbccdb4f820ed285a451c9dceb6223a0667` |
| `lean/UnifiedEventDensity.lean` | `b552274d799b3b192daafee66287c74496699304e72ec89a2159f276a3b5da89` |
| `lean/SemanticPayloadOpeningView.lean` | `bb3a10730f44cd10abeb0e581a818365963512841a4e4d7b4be6542760d57454` |
| `lean/TraceAppend.lean` | `6f7698cd716b83ca639a4a43d6a98fbf12cf3e18c097fc13a18faf1e118f8f0b` |
| `lean/RawRoundAppend.lean` | `b63d8fa49497308909051fb24708a46847496f8e70f0836c021bd6c2e0f41610` |
| `v8-fs-generic-20261006/lean/FS2/Duplex.lean` | `3a2c1330dfd39d59b10cdf1fc68b218432775b855c98e700d1ba938eeac2d88b` |
| `crates/aspis-r1-cost-probe/src/semantic_wire.rs` | `58c671cee016246aa464a35ba443009813581e4a53bce37dd528d048009f2db7` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-r1-cost-probe/src/host_semantic.rs` | `113a367ae1e01d8fbd808ce3756b87040fd31ab359d94bad50b7c55c89c284bf` |
