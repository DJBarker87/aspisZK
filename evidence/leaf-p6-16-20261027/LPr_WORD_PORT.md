# Native word port, stage 2

LPr_WordValue.bits (L011) and LPr_WordNat.value (L012) establish the
exact native U32.from_le_bytes value on FOUR ARBITRARY U8 values, without
canonicality, output success or accepted-run assumptions. The latter is
precisely a.val + 256*b.val + 65536*c.val + 16777216*d.val. This supplies
the missing library arithmetic port identified by LPq. No multiplier stub.

L001-L004 rejected representation/cast proofs; L005 exits0 BUT IS EXCLUDED:
its default bv_decide proof has a nonstandard native checker axiom.
L006-L010 rejected normalization/explicit-argument attempts. L011 replaces
that method with 32 small bit-coordinate cases, kernel proofs only.
L011/L012 axioms subsets of propext/Classical.choice/Quot.sound.
No timeout/memory kill or unchanged failing-shape rerun.

L011 wall2.578284843s RSS2649028KiB swap0; L012 wall1.293546284s
RSS2638020KiB swap0, both exit0. Full receipt/source/dependency hashes,
revision, cgroup and commands in LPr_L011/ and LPr_L012/.
Aeneas objects selected through LEAN_PATH are pinned in LPr_LIBRARY_PIN.json.
This is a library/source helper, not complete prepared_claim closure.
