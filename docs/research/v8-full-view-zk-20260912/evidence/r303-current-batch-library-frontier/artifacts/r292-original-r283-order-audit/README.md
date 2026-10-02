# Structural audit of original R283 declaration ordering

The exact original R283 LLBC (`has_errors=false`, SHA-256
`999fdb4f5a034faf9d4aa11c7a44851b9c79f471d76ae6afb3b92aed0767c8d5`) already
contains 109 `translated.ordered_decls` groups. The audit resolves all 111
listed declaration IDs to non-null rows in the corresponding five declaration
tables, finds no malformed group entries or duplicate IDs, and confirms the
local body root is `Fun 0` in group 107 as `{"Fun":{"NonRec":0}}`.

The original `Rec` groups are exactly:

- `TraitDecl Rec [1, 7, 0]`
- `TraitImpl Rec [4]`, `[15]`, `[11]`, and `[2]`

The singleton trait implementation metadata identifies `[11]` as
`core::iter::range` at file id 28, line 980, and `[2]` as
`core::slice::iter` at file id 21, line 153. Those are present in the original
order. The pinned Charon reorder source hash is
`8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632`; its
`is_non_rec` rule is at lines 458–469. This report validates serialized group
shapes and declaration ID resolution; it does not recompute SCCs or assert a
source theorem.

The failed R288/R290 manual subset-order attempts are separate metadata
diagnostics and unnecessary for this original input, which already has
Charon's SCC group serialization. Their diagnostic history remains preserved
in their respective scratch directories; this audit does not replace or erase
it. No translation or build was run by this audit.
