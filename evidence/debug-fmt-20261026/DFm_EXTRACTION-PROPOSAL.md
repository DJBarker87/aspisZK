# Proposed extraction configuration — not applied

The selected record parser is header-array F, not the older option E variant.
DFm_generated-variants.json proves the retained replay source is byte-identical
to the committed header-parser-f source; the prefix source matches all three
committed prefix-e-exact copies. The patch targets the canonical Lean source
copies, and DFm_patch-targets.json records original and filtered hashes.
DFm_prepare.py --check and `git apply --check --unidiff-zero` both pass. Neither
command applies the patch. Stage 1's option-E provenance was incomplete: that
older sibling also derives Debug, but DFm_extraction-provenance.json now pins
the actual selected F and prefix-E crates and their extraction commands.

Both Rust Error enums derive Clone, Copy, Debug, PartialEq, Eq at lib.rs:131.
The historical extraction roots cover the whole r1_wire module, admitting its
derived Debug impl. Aeneas emits Error.Insts.CoreFmtDebug.fmt and its trait record
in Funs.lean. They import Aeneas directly, not a generated FunsExternal module.
The actual Formatter axiom is in Aeneas/Std/Core/Fmt.lean:13; formatter methods
are placeholder definitions. Aeneas/Std/String.lean:28 supplies `toStr`'s default
bound proof using `decide +native`. Each derived fmt has 18 toStr occurrences:
Allocation, RowOrder, expected, actual, InvalidRow, Tag, row, Length, row,
NonCanonical, row, value, Boundary, round, Terminal, EqualCirclePoints,
TrailingBytes, Public. Elaborating them introduces the 18 named native axioms
and 16 proof helpers per parser. This is the source of the full 37-name finding;
there are not 37 hand-written parser axioms.

Proposed command additions to BOTH recorded Charon cargo invocations:

```text
--exclude 'core::fmt::Debug'
--exclude '{impl core::fmt::Debug for _}'
```

The pinned Charon source documents --exclude as "not translate at all";
name_matcher/parser.rs accepts `{impl Trait for Type}`, and name_matcher/mod.rs
has explicit first-Impl matching across crate-qualified paths. These source
excerpts and their hashes are in DFm_charon-options-provenance.json. This is a
concrete, source-supported proposal, not a tested extraction-config adoption:
the pinned option documentation also warns that trait-impl filtering may only
filter methods. Verify that the impl record is excluded too; do not accept an
opaque replacement or add an external fmt premise. If this version retains the
record, implement a narrowly scoped Debug-trait exclusion in its extraction
configuration, or restrict the extraction roots to the actual parser entry
points and required type closure. Keep all non-Debug derives and Rust parser
source unchanged. Do not change general unsafe/drop handling or arithmetic.

Acceptance for future extraction: no CoreFmtDebug declarations or associated
native axioms in the two output module ownership contexts; every retained
expression matches the present candidate modulo explicitly audited compiler
helper renaming and bound-variable names; all direct consumers recompile; full
closure replay and actual-top axioms audit succeed under their separate gates.
The shared axiom-free Error matcher may move when Debug disappears, so merely
searching for its former qualified name is not a semantic comparison. Keep
that functionality via the automatically regenerated equality matcher.

No Rust/Charon/Aeneas re-extraction was run here; these are source-filtered
candidate copies. No production source, config, ELF or research-generated file
is modified. The three historical ELF pins are retained, not remeasured.
