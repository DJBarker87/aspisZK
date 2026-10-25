# Source-node and recovery transport

Checked helper results, NOT accepted SDK closure:

- SdkC_NativeNode.source_leaf/source_node: exact installed leaf and concrete
  native parent-node Results, including partial hash failure/divergence.
- SdkC_Oracle.accepted_exact: exact ordered successful read log (duplicates
  retained) and value for accepted literal source syntax in the ideal world,
  from existing P1/success-only RuntimeSyscall. No total oracle added.
- SdkC_Progress.rows_eq_source: exact bounded native node-loop Result under
  the same success-only primitive law, deriving each reached node's progress.
- SdkC_GlobalRecovery.indexed_recovery_or_collision: transport an exact
  indexed path with contained reads and root/frame provenance to recovery
  strictly before the first commitment read, OR the charged collision event.
  collision_bound exposes 6 Q^2 / 256^32 for the containing adaptive program.

The last theorem still has explicit source-read containment, parsed-wire,
prepared-root/frame provenance and global query bound. It does not discharge
these by a structure or assert that independent local logs form the SDK log.
No arbitrary ChildConeJoin premise has yet been removed from Op5T_Final.

All successful module receipts have only propext/Classical.choice/Quot.sound.
Attempts003,005,008,009,010,012 failed with elaboration/type errors;004,006,
007,011,013 passed after source corrections. No timeout/memory kill/cap raise.
Full source hashes, dependencies, source revision, exact target/command,
wall/exit/RSS/swap/axioms are retained per attempt. No package replay/Kani.
No source, failure-event, adversary or cryptographic assumption changed.

Source inspection then found Port9OR_Batch's existing complete physical source
reification. Reuse it rather than duplicating whole-batch syntax. Its missing
unchanged dependency closure is pinned in SdkC_batch_dependencies.json and is
being built one module per attempt. This is proof dependency compilation,
not a change to the launcher or monitoring infrastructure. No cached object
is overwritten; only missing unchanged objects are added.
