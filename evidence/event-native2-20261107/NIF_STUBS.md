# NIF stubs and reused laws

NIF uses the NIC per-limb natural-value reference constraints unchanged except its module prefix. No field multiplication is verified in Kani.

| Stub | Paired Lean theorem | Domain |
|---|---|---|
| m31_product_spec | AspisR1.NIC_FieldStubs.m31 | all U32 operands |
| wide_product_spec | AspisR1.NIC_FieldStubs.product | canonical E operands |
| wide_add_spec | AspisR1.NIC_FieldStubs.add | canonical E operands |
| q_subtract_spec | AspisR1.NIC_FieldStubs.subtract | canonical Q operands |
| wide_scale_spec | AspisR1.NIC_FieldStubs.scale | canonical E; arbitrary U32 scalar |

The complete table of raw/Q/mixed stubs inherited in inactive NIC harness source is NIC_STUBS.md (pinned in NIF_REUSED_INPUTS.json); those inactive harnesses earn no new credit. Current fold windows call only the five stubs above. Native any_e generates arbitrary canonical E. NIC_FoldDomains.circle/line supply total source cuts and SAME-site canonical intermediates; add/sub closure is supplied by the exact NIC_FieldStubs value laws and their NFS constituents. Scalar inverse operands may be arbitrary U32. There is no successful fold premise.

KMX_copy_stubs.patch is exactly bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. K003 copy_positive passes; K004 inverted copy control fails in this scratch configuration. Every new native pair has a reachable digest control. Other runtime-frontier unreachability mappings are byte-identical modulo NIF prefix to NIC's calibrated mappings. No contract/stub_verified, writable static, Option<fn> observer or new copy stub is introduced.

Natural-value equations and effect absence have separate roles. Scope limitations and any unjoined source boundaries remain in NIF_REMAINING.md; a stub alone never proves an enclosing source effect join.
