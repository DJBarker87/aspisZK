# NBI multiproof bridge

**OPEN. No headline premise removed.** Exact joint domain and full Result,
scratch and chronological digest-log target: NBE_multiproof_BRIDGE.md,
frozen Rust 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, Arity Two, 1<=d<=16,
physical length<=5504, strictly increasing canonical input indices; BOTH TX1
n10 and TX2 n12. Inherited NBE proofs/gates are imported/read-only.

## Local progress

- NBI_K001 reads an arbitrary sibling at an arbitrary cursor in an arbitrary
  5504-byte surrounding state. It includes short rejection, all selected
  bytes and pointer/length identity; no 64-byte window restriction.
- NBI_K002 checks one actual idx write with arbitrary unread/consumed state.
  K004 checks the supplied cursor updates and their preserved bounds.
  K030 is the repaired single digest-write gate and passed.
  K003 is EXCLUDED: unwind2 failed in construction of an arbitrary nested
  array, not in a source safety/property assertion. K030 changes its setup
  to unwind34. This is neither a timeout rerun nor a timeout/cap increase.
- NBI_Frame.write_ext / unread_after_write / finish_exact prove full owned
  array frames, unread-tail retention and exact installed post-hash writer.
  NBI_Window.supplied_observation composes physical read, reply, address,
  ordered singleton log and scratch on the same state. These split NBE K016's
  mutation obligation; they do not pretend its timed-out whole row passed.
- K005/K006 check one equal-parent count-scan increment and one group commit.
  NBI_CountScan.scan_boundary / binary_group / scan_group prove the finite
  inner scan and derive the one/two-group-width precondition from strict
  unread order. Existing CountPhysical/CountPhysicalLevels induction is reused.
- K007/K008 check one ordering-window/range cell; K010 one initial copy cell;
  K011 pair/advance; K012 end-of-level scalar reset; K009 actual final
  root/index/count/cursor conjunction. These are atomic source gates.

## Exact open members

1. NBI_NativeCountScanPort: associate native initial slice copy, total
   well_formed scans and all physical/scalar count states with the inherited
   count-row/height recurrences. NBI_Admission.admission_iff now identifies
   the total natural adjacency/range scan with wellFormed; NBI_CountPort.scan_row
   ports inner-scan cursor/contribution to the inherited physical count row.
   Native iterator/copy and the complete source control port are still needed.
   The inner group induction is supplied, but
   no whole native node_count result is claimed from isolated atomic gates.
2. NBI_NativeNodeGatePort: combine paired/short NBE rows and the split supplied
   selection/writes/callbacks on the SAME physical carrier with every checked
   scalar/array operation of MultiproofConePhysicalProgram.node/nodeWith.
   The supplied physical read and post-hash update are now locally proved;
   the complete native-row port is still not instantiated as NodeGate.
3. NBI_NativeVerifyControlPort: derive admission/next-level domains and bind
   actual n=w/height control and final conjunction to Port4B_VerifyInstall,
   consuming the inherited 18-level induction. One scalar reset check is not
   a one-level native refinement. No whole-buffer harness is run.

No full unit, TX2 U09, S2 or deployed 100-bit closure is claimed. Runtime,
oracle-value, heap/allocator/ABI, source lowering and ELF obligations remain.
