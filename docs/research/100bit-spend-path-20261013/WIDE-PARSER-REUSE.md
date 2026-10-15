# WideExact parser reuse inventory

This note records the existing Lean results reused to prove the retained
32-byte `WideExact` parser model and the exact candidate adopted on the
research branch. Compiler correctness and the complete verifier caller path
remain outside this parser checkpoint.

The baseline Rust source recorded in this inventory is
[`crates/aspis-core/src/field/wide_exact.rs`](../../../crates/aspis-core/src/field/wide_exact.rs),
SHA-256 `56c26ce33cd0caee95f33474bfc351c5409503b6af665dba7c8837d6ec1068ea`
at baseline source revision `aba310f1daa065a27da89d15c6c47166037a8a71`. The prior R0-wideexact
source snapshot is pinned by
[`results/r0-wideexact-20261009/source-manifest.json`](../../../results/r0-wideexact-20261009/source-manifest.json):
revision `73c502add062f5267146827117b4d1cf577475ab`, with
`crates/aspis-core/src/field/wide_exact.rs` SHA-256
`622df5493a777ea2d97efedf5353b5fe877f8066abd2fa595055d02da773c428`.
The full-file hashes differ, but direct extraction from each file shows the
two method bodies are byte-identical. The extraction starts at each method
signature and ends at its matching outer brace, excluding preceding comments
and whitespace:

| Rust method | Baseline and historical body SHA-256 | Literal behavior |
| --- | --- | --- |
| `WideExact::from_limbs` (`wide_exact.rs:207–234`) | `bce2506d3fad8aa068bee648ea792ae74950d263e61a3542cffe92c81106b131` | Accepts `[u32; 8]`; returns `None` if any limb is `>= P`; otherwise assembles two QM31 coordinates in limbs 0–3 and 4–7. |
| `WideExact::from_le_bytes` (`wide_exact.rs:254–260`) | `e5beddf2508299af58a01e286ce6bc60018d4224f372013ac36af73dfb96b841` | Requires exactly 32 bytes via slice-to-array conversion; decodes eight consecutive little-endian u32 words; passes them to `from_limbs`. |

The closest checked eight-limb mathematical representation is
[`R0C.ModuloField.digitsField`](../v8-r0-close-20261007/lean/R0C/ModuloField.lean),
whose type is `(Fin 8 → Fin P) ≃ WideExact`. Its `digitsField_apply` theorem
states, without extra premises, that it maps the first four residues through
`decode4` into the low coordinate and the last four through `decode4` into the
high coordinate (`ModuloField.lean:26–41`). The same file defines
`fieldRank : Fin (P^8) ≃ WideExact` (`:43–44`) and byte-block ranking for a
32-byte `State` (`:19–24`); these are field/cardinality and sampling models,
not parsers for `WideExact::from_le_bytes`.

`WideTower.lean:62–76` defines
`WideExact := QuadraticAlgebra QM31Exact wideU 0` and proves
`wideExact_card : Fintype.card WideExact = P^8`. Its direct imports are
`AspisV8R15.ExactTowerFinite`; the direct imports of `R0C.ModuloField` are
`R0C.ModuloCounting`, `AspisV8R19.R599CanonicalFieldTuple`, `WideTower`,
`AspisFormal.CircleGroupOrder`, and `Mathlib.Algebra.BigOperators.Fin`.
Source hashes: `WideTower.lean` `4dfa22ed26400c6067917a25ff51f809554b852a69763c4c8f22959e221ab4fc`;
`ModuloField.lean` `2c0f918c9eb6ac2ab93e07f955d3a5423a968dcefa01fcde58b31feb19d86594`.

Other checked declarations give nearby pieces, with narrower types:

- `AspisV8R19.SamplerFieldDecode.decode4` maps four `Nat`s to `QM31Exact`,
  and `decode` accepts a `List Nat` but returns zero unless the list is exactly
  four items (`SamplerFieldDecode.lean:10–13`).
  `decode_zero_iff` additionally requires length four and every element `< P`
  (`:48–55`). This is four-limb QM31 algebra, not an eight-word byte parser.
- `AspisV5ComponentCQM31Representation.decodeWordLE` takes four
  `Fin 256` bytes and returns a bounded raw u32; `decodeM31LE` returns
  `Option M31Value` and rejects values `>= P`; `decodeQM31LE` takes 16 bytes
  and returns `Option QM31Limbs` after checking all four canonical M31 words
  (`V5ComponentCQM31Representation.lean:58–105,123–178`).
  The file SHA-256 is `a1be2908debd5f94bbb3570132a89818f582e061691b508557ad7e52691fb283`.
- `AspisR1.RetainedFieldByteCodec.decodeM31Bytes` wraps a list with exact
  length four, and `decodeQM31Bytes` wraps exact length 16;
  `AspisR1.ListFieldCodec` supplies success round-trip and successful-decode
  re-encoding lemmas (`lean/ListFieldCodec.lean:29–86`,
  SHA-256 `c30eeb96043b627a2fb240777bae9f31b7b4a01e86f1ccd129acf415877f7b7a`).
- `AspisV5ComponentCQM31TowerExact.qm31ExactLimbEquiv` maps four canonical
  limbs to `QM31Exact`, with inverse theorems (`:138–172`).
  `decodeQM31ExactLE` is still the 16-byte/four-limb decoder
  (`:207–217`, file SHA-256
  `75404d16b5a71f67146b91ca35739b111f81bb730beb77432267f2b5385cebe5`).
  `AspisV5ComponentCExactTowerDeployment.decodeQM31ExactLE_to_limbs` proves its
  decoder commutes with that four-limb representation (`:40–47`, file
  SHA-256 `6495cdf2d07a39d3204d101edff5be9253ebc9c96a0b96ac0af459082ad725d9`).
- The separate strict candidate QM31 bridge is checked for fixed 16-byte
  arrays by
  [`CandidateStrictQM31Parser.source_refines`](lean/CandidateStrictQM31Parser.lean)
  (source SHA-256
  `aeed259da29e525670c23e4a05341d563d3584c5a2f98bbd83c6b84fb57c390d`). It
  can be reused on two 16-byte halves; the candidate chain below supplies the
  explicit split/join and outer parser model.

## Checked two-half parser model

The retained Lean chain is now recorded in the focused seven-module
[checkpoint](evidence/lean-candidate-wide-checkpoint-20261015/README.md):

1. `WideParserArrayHalves.slice_half0`, `slice_half1`, `half0_bytes`, and
   `half1_bytes` connect the two 16-byte array slices to the corresponding
   halves of the 32-byte list representation.
2. `StrictWideByteCodec.decodeWideLE_encodeWideLE`, `successful_halves`, and
   `encodeWideLE_of_decodeWideLE` establish codec round-trip, successful
   halves, and byte reconstruction for the strict fixed-width list model.
   Its `WideLimbs` type embeds canonicality. Dynamic slice-length rejection
   and successful-parse length are handled by the outer parser theorems.
3. `WideExactLimbCodec.pairExactEquiv_apply`, `pairExactEquiv_injective`, and
   `pairToExact_eq_digitsField` connect the two decoded QM31 limb tuples to
   the existing exact `WideExact` representation and `digitsField` model.
4. `CandidateWideParserSource` retains the Aeneas-translated candidate parser
   bodies. `CandidateWideParserRefinement.wrong_length` and `source_refines`
   prove the isolated two-half candidate's wrong-length result and its exact
   relationship to the strict decoder model on fixed 32-byte arrays.
5. `CandidateWideParserContracts.total`, `fixed_success`, and
   `slice_success_canonical` establish totality, successful-decode byte
   reconstruction, and canonicality of both returned QM31 halves. No
   canonical-input premise is required.

The separate [unrolled strict bridge](lean/UnrolledWideParserRefinement.lean)
(source SHA-256
`e057b44f28ffb7b398c9439c6945ce7ab05537053f956dd4c70b28016cc00aa6`)
is now green with six standard axiom reports. It proves that the unrolled
candidate agrees with the old two-half parser on every slice, refines the
strict 32-byte list decoder on every fixed-size array, and is total on every
slice. A successful parse implies exact length 32 and canonicality of both
QM31 halves without a canonical-input premise; on a fixed-size array,
successful parsing also reconstructs the original 32 bytes from the decoded
limbs. These are Lean model statements for the retained extracted candidate. The final combined checkpoint is now green; the research-branch adoption is recorded below.

`ROOT-VALIDATION.json` records 21 focused attempts, including 14 retained
failures, seven successful target modules, 38 successful axiom reports, 19
checkpoint public items, and a passing source-retention checker. The scope is
the exact retained two-half candidate model. It does not establish Rust or
compiler correspondence, caller behavior, or verifier/security closure.

The isolated candidate history has distinct outcomes. The half-parser `d`
candidate and inline `g` variant failed the SBF stage-1 budget gate; see
[`wide-parser-v152-cost-20261015`](evidence/wide-parser-v152-cost-20261015/README.md)
and [`wide-parser-inline-v152-cost-20261015`](evidence/wide-parser-inline-v152-cost-20261015/README.md).
The selected h2 unrolled candidate passed its recorded finite optimized native
differential and a 13-pair v0 transfer cost gate; see
[`wide-parser-unrolled-differential-20261015`](evidence/wide-parser-unrolled-differential-20261015/README.md)
and [`wide-parser-unrolled-v152-cost-20261015`](evidence/wide-parser-unrolled-v152-cost-20261015/README.md).
The 13-pair cost result is limited to that fixture and scenario. Four larger
transfer/withdrawal cases at 255 and 1023 pairs also passed local acceptance
and settlement checks; their exact fixtures and measurements are in
[`wide-parser-unrolled-large-cases-20261015`](evidence/wide-parser-unrolled-large-cases-20261015/README.md).
The strict Lean refinement and combined checkpoint are checked as described above. The adopted research-branch runtime parser is h2 at SHA-256 6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b; the previous baseline was 56c26ce33cd0caee95f33474bfc351c5409503b6af665dba7c8837d6ec1068ea.


## Research-branch adoption status

The root adopted the exact h2 unrolled WideExact::from_le_bytes implementation on the research branch. The current file crates/aspis-core/src/field/wide_exact.rs hashes to 6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b; crates/aspis-core/src/field.rs remains at 28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea. Adoption metadata is in [adoption.json](evidence/wide-parser-adoption-20261015/adoption.json), and the exact patch is in [runtime.patch](evidence/wide-parser-adoption-20261015/runtime.patch). The adoption record reports 457 other package-manifest entries matching and one test-only manifest difference.

The final [unrolled-wide checkpoint](evidence/lean-unrolled-wide-checkpoint-20261015/source-manifest.json) records 12 standard-only axiom reports. Its selected theorem target proves retained extracted-model relationships; it does not establish Rust compiler correctness or whole-verifier/security closure. Earlier baseline evidence and cost outcomes above remain historical; adoption does not rewrite those snapshots.
