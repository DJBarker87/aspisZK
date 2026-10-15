# WideExact parser reuse inventory

This note records checked Lean structures that may be reused for a future
32-byte `WideExact` parser bridge. It is a source inventory, not a parser
refinement or Rust/compiler correspondence claim.

The current Rust source is
[`crates/aspis-core/src/field/wide_exact.rs`](../../../crates/aspis-core/src/field/wide_exact.rs),
SHA-256 `56c26ce33cd0caee95f33474bfc351c5409503b6af665dba7c8837d6ec1068ea`
at source HEAD `6e25cda9d35e52df0980dbcd6744522bd3caaab0`. The prior R0-wideexact
source snapshot is pinned by
[`results/r0-wideexact-20261009/source-manifest.json`](../../../results/r0-wideexact-20261009/source-manifest.json):
revision `73c502add062f5267146827117b4d1cf577475ab`, with
`crates/aspis-core/src/field/wide_exact.rs` SHA-256
`622df5493a777ea2d97efedf5353b5fe877f8066abd2fa595055d02da773c428`.
The full-file hashes differ, but direct extraction from each file shows the
two method bodies are byte-identical. The extraction starts at each method
signature and ends at its matching outer brace, excluding preceding comments
and whitespace:

| Rust method | Current and historical body SHA-256 | Literal behavior |
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
- The separate strict candidate QM31 bridge is now checked for fixed 16-byte
  arrays by
  [`CandidateStrictQM31Parser.source_refines`](lean/CandidateStrictQM31Parser.lean)
  (source SHA-256
  `aeed259da29e525670c23e4a05341d563d3584c5a2f98bbd83c6b84fb57c390d`). It
  can potentially be reused on two 16-byte halves to obtain two four-limb
  values; that application would still need explicit split/join and outer
  parser plumbing.

I found no checked Aeneas-generated Lean body or theorem for
`WideExact::from_le_bytes` or `WideExact::from_limbs`, and no `UW31` or
`WideExact8` Lean aliases. The literal strings `WideExact8` in older search
results are part of mangled Rust method symbols, not type aliases.

The remaining parser-specific gap is the connection from a 32-byte slice to
eight ordered little-endian words, exact-length rejection, the all-eight
canonicality check, and `Option` assembly into `WideExact`. The canonical
`Fin 8 → Fin P` domain of `digitsField` supplies the eight-limb mathematical
representation once those words have been decoded and shown `< P`; it does
not itself prove that byte-parser control flow or source implements that
mapping. The current strict QM31 theorem does not close this outer 32-byte
parser edge.
