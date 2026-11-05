# NHY stubs and domains — snapshot stage

| Stub | Paired Lean law | Domain / effects |
|---|---|---|
| borrowed_oracle | NHY_SnapshotJoin.both_arms/rejected; NHY_SnapshotRoot.returning; accepted S2TrustedSdkBorrow15 | SAME account receiver and borrowed source descriptor, explicit Ok(original slice) or Err(AccountBorrowFailed), arbitrary Bool, local receiver/pointer/len/reply log. No success assumption. SDK typed-guard/deref/drop semantics are the accepted SDK row and retained NHJ native bracket. |
| clone_oracle | NGL_CloneDomain.clone; NHY_SnapshotHeader.clone_domain/clone_reply | SDK Err establishes soleABF; native stub deliberately permits either canonical ABF/IAD reply and logs exact temporary error address. The paired child law selects exactABF. Modifies local records only; NHD_K014/015 actual clone/control reused by SHA. |
| KMX ptr copy | retained KMX_CopyMeaning + NHJ_CopyPacket initialized/contents + NHD_SnapshotWindows | Exact patchbcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. K005 PASS/K006 one failed ensure, same configuration; native copy/allocation/capacity/finalize/frame predecessors retained by SHA with matched controls. No custom copy oracle. |

No field multiplication or writable static. No stub_verified Result interface, no Option<fn> credit. Runtime/allocator abort/divergence and retained std/compiler/ABI/P6 realization remain explicit. The successful reference branch is specialized only after SDK15 derives success from SAME related valid Entry.heap, whose counter is computed zero; no successful-borrow premise is added. Root physical relatedness is not discharged by this leaf, and enclosing callers still owe their SAME-input domain links.
