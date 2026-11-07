# NMB stubs and domains

No field-multiplication stub or new multiplication proof is used. No SHA/digest syscall body is unwound. No verified stub on Ref, RefMut, Result<Box>, ProgramResult, Option<fn> or a writable static is used.

| Stub | Domain and use | Paired evidence / disposition |
|---|---|---|
| canonical KMX_copy_nonoverlapping | reached copy builtins in every Kani configuration; exact patch SHA bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 | existing KMX Lean laws retained; local positives have matched negatives where credited; no handwritten copy replacement |
| NMB_fill<N> via stub_verified | initialized existing mutable byte array, N=58295/1880/1768; weak modifies-destination contract gives arbitrary initialized input contents | K004–018 three five-control fidelity families; input generation ONLY, not a frozen callee bridge or resource packet |
| K001 plain snapshot/owned-child oracles | full arbitrary buffers and selected descriptor observer in actual-parent diagnostic | timeout, retired; no credit or packet installation |

The full logical array Cut is only a required model condition. K030 header/frame evidence alone does not distinguish all ProgramError variants; K034 does not independently control the exact-error supplement. The source snapshot owns its complete returned buffer only through the CLOSED343 packet at that packet's own domain and the SAME NLF SDK chain; this native association is not supplied by an oracle or by integer pointer equality.
