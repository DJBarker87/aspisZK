# R293 sourceful-stdlib batch extraction

R293 extracts the same frozen source/root as R283 (`batch` only) and retains
the exact Cargo features, Rust flags, Charon preset, cached optimized release
build, and resource caps. The only extraction-option change is the explicitly
selected include coverage: `core::option`, `aspis_core::field`,
`core::iter::adapters::chain`,
`core::iter::traits::iterator::Iterator::any`,
`core::iter::traits::iterator::Iterator::chain`, `core::slice::iter`, and
`core::slice::_::last`. The fresh output path/unit/slice names are R293-specific.

The purpose is to inspect these selected source bodies/type instead of the
opaque declarations seen in R283. It is an extraction diagnostic only. The
bundle records Charon `has_errors`, root presence, and a census of selected
body/type declarations. It does not translate, fill external templates, or
claim acceptance or semantic correspondence.
