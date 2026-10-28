# NCB substitutions and domains

KMX patch sha256: bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. Bodies are imported verbatim from evidence/kani-mitig-20261028/KMX_copy_stubs.patch, through the retained NBS_copy modules or NCB_copy in the program scratch. No own copy stub. K001 and K012 fail the intended false-copy property in core/program configurations respectively. The r1 configuration will receive its own control before credit.

| Stub/cut | Paired theorem | Domain/limit |
|---|---|---|
| KMX copy/pointer-copy/clone/extend/to_vec/realloc | KMX_CopyMeaning.loop_spec, copy_frame, append_spec, realloc_prefix | Copy values, valid aligned regions, nonoverlap, equal slice sizes, valid allocator layouts/ownership. Value laws do not prove arbitrary allocation capacity/pointer/cleanup semantics. |
| NCB_digest.reply replaces runtime hashv | AspisR1.NCB_DigestTotal.reached, existing F3U_Oracle.syscall | SAME valid native parts; SHA value is existing runtime trust row. Native K013 checks forwarding for0..3 parts with lengths0..4 and arbitrary reply, without SHA execution. This does not establish all reached request validity/chronology. |
| NCB_prefix.mul replaces M31::mul | AspisR1.LPf_BaseMultiply.source | All u32 operands, return ok exactly natural product modulo2147483647. No field multiplication proved in Kani; stub assumes the natural spec. |

The generic model completion NCB_DigestTotal.total proves infallibility of the adopted oracle dictionary. Native per-call routing, caller memory validity, chronological same-execution association and runtime effects remain distinct obligations. No stub or cut supplies a complete native parent result.
