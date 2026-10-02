# R278 private inverse raw adapter

`AspisR278PrivateInverseRaw.lean` imports `AspisR249R110Raw` and the pinned R156 `FunsCore`, opens both namespaces, and copies exactly three complete generated R276 declaration blocks: `B.ZERO`, `B.neg`, and `B.inv`. Their documentation, attributes, signatures, and bodies are retained verbatim; the generator records zero replacements. The adapter declares no B/P/sub/M31 shadow definitions. It includes `#print axioms` commands for all three declarations and was not compiled or staged.

The direct and recursive helper inventory is in `binding-audit.json`. It compares all requested R276 helper definitions against existing imported declarations after whitespace normalization:

- R249 `P110` is text-identical; R249 `B.sub` differs only in two existing API qualification spellings, `core.num.U32.` versus `Std.U32.`.
- R156 `field.P`, `reduce_u64`, `M31.mul`, `square_n_loop.body`, `square_n_loop`, `square_n`, and `M31.inv` match, allowing exactly one existing `M31.mul` adapter: `31#i32` in R276 to `31#u32` in frozen R156. The count is one on each side and the shift count is unchanged.
- The R276 and R156 `M31` representations are both `Std.U32`; R249's B representation is also `Std.U32`. R278 defines no B or M31 type.

The three copied roots have matching definition-block hashes in R276 and R278, and the generated full source blocks are captured in `raw-adapter.json`. `binding-audit.json` records declaration hashes for each helper and reports no unresolved local helper declaration. External Aeneas support names (`Result`/`lift`, U32/U64 operations and casts, `massert`, Range/Iterator/loop, `done`/`cont`) are listed as imported support references; no implementation or semantic claim about those APIs is made here.

This is a mechanical binding audit only. The lead owns the source correspondence and semantic decision. No Lean compilation was run.

R276 Funs SHA-256: `3e3a3ee0630af9de63601a448c2a240e0f31fc6712de6def854c72de1e6b0269`.
R249 raw SHA-256: `f38d892beef83cba109b007a5d5b6851629ead6acc736d2fbff1c25a530f72cd`.
R156 FunsCore SHA-256: `5ef8405549c6feff405715a6697ffff9a370610d5dc116fc452a1046fae0c1f2`.
R278 Lean SHA-256: `d3dd885a9225821f9e584ec4cabd178c1e6eafcde1d2470df2644e5cf23b16be`.
Raw adapter report SHA-256: `f11b723ddb13fee71a0e1f82853e3c9105d1fe2b072efae8db17231c44b7bf52`.
Binding audit SHA-256: `a055a6389845a94f805496139e493c4df0a606b20b65390d2bf96ba97a0429cd`.
