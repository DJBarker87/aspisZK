# Input/setup corrections

L001 was rejected by the private client before launch: NFS_NEV_CtorResults is packaged inside NFS_AccumPart00, not its own exported object. Charged conservatively. L002 imported the old NEV_CodeFieldBridge, which pulls a legacy Prepared owner; L003 uses the canonical NFS namespace and passes unchanged intended inspection. No shared tool/cache was edited.

K001–003: missing frozen workspace/path manifests. K004–005: missing frozen Rust include files. K006: scratch root lacked cfg(kani) allocator_api for the exact KMX patch. Each is compile/setup-only, no semantic credit. Frozen support files were restored from the pinned git revision; K007 is the first solver-submitted constructor pass. The private source generator now adds the required cfg-only attribute. Graph validation is unchanged and every native launch retains the frozen offline graph and post-lock check.

The initial stage-0 handoff mistakenly grouped five field helpers among this job targets; exact NHH_TARGETS.md correctly identified nine constructor rows instead. The stage-0 handoff has been corrected; no helper proof was launched.
