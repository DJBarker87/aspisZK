# Unrolled Wide parser source retention

The retained Lean module contains the three h2-generated nonopaque functions under explicit names ending in `_unrolled`. It imports the checked candidate Wide parser source, reusing its WideExact type, the imported candidate field types, `field.P`, and `BYTE_LEN`. The checker compares all six shared declaration blocks byte-for-byte (including generated source comments) against h2 output before checking that the retained function blocks differ only by the approved Lean identifier renames.

The focused NUC compile passed: `UnrolledWideParserSource`, attempt `unrolled-wide-parser-source-a`, exit 0, wall 1.51s, max RSS 2,596,452 KiB, swap 0, cgroup 4G/6G/0. Its three public declarations report only `[propext, Classical.choice, Quot.sound]`.

This is generated-source retention. It establishes neither execution refinement nor runtime adoption. Source inputs, h2 LLBC/generated metadata, imported sources and objects, exact attempt artifacts, runner snapshots, and deterministic final-object archive are pinned in `manifest.json`.
