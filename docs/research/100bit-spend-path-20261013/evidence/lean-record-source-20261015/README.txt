Coordinator checks of exact row_shape and parse_record extraction, 2026-10-15

Row-shape Types/Funs: exit0,16.383/17.449s, sampled group2727936/2767392KiB.
Initial parser E Types/Funs: exit0,22.942/18.955s, group2438176/2600096KiB.
The E26-declaration audit compiled,6.389s/2780624KiB, but its target parse_record
still depended on Aeneas.Std.core.fmt.Formatter via the impossible header unwrap.
Its unused derived Error.fmt also carries Formatter and native.decide axioms.
These qualifications prompted the actual source header-array rewrite.

Final parser F has unchanged Types (source byte-equality checked), reused from
E; no Types replay. First Funs check failed because the new namespace overlay
needed its own copied Types.olean, despite the older overlay on LEAN_PATH.
The copied object's exact hash/provenance is in reused-types.json. Corrected
Funs check: exit0,11.153s/2757776KiB. F26-declaration audit: exit0,16.974s/
2745568KiB. parse_record now reports ONLY propext,Classical.choice,Quot.sound.
All other audited declarations are standard/empty EXCEPT unused Error.fmt,
whose Formatter/native.decide axioms remain openly recorded. Derives were not
removed. There is no claim that every emitted declaration is axiom-free.

The helper-parser saved-proof counter passes1 onbc7ec2be8. After the header
rewrite, two differential parser tests pass and the saved-proof counter passes1
onc111cbbf2. Final native wall3.991/8.807s, group295376/289920KiB. The counter
retains328/349 stage1 and465 core stage2 with next=0; it does not measure PDA
runtime hashes or prove the universal source bound.

All recorded process swaps are zero; system swap absence is not asserted.
The full commands, source hashes/revisions, failures and final outputs remain
here. Runner source_base_revision is a historical base label; checkout_head
plus source_sha256 identify checked bytes. Compiler/backend4.31 cache provenance
and limitations are referenced in pins.json. No4.32 backend build was attempted.

Compilation/audits are not parser correctness, Prefix::parse correspondence,
Rust extraction correctness or a4.32 integration theorem. Those stay OPEN.
The separately checked all-U8 row theorem and serializer success theorems have
their own retained evidence. No unchanged manifest replay was run.
