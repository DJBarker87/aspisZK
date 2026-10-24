# Exact source association and remaining P6 boundary

This is a source audit, not a Lean theorem or verified event contract.
`source.py --check` checks immutable selected bytes against the original file;
`source-map.json` pins full source, prefix-through-factory and each selected item.
Factory selected lines31–58 correspond to original211–238. Types, error From,
limit16 and nonzero helper are exact included items. No source Result or ownership
behavior changed. Unreferenced methods/imports are omitted, not stubbed.

Fresh Charon049 (built MIR, precise drops, unchanged zeroize included) emits
factory function4 and StateOnlyAttemptSecrets glue31. Expanded `source-audit.json`
retains complete signatures, local types and drop targets. Factory locals11/21/23
are bytes64/field32/leaf32. Seven syntactic normal-context Drop statements are
not seven runtime drops: IDs677/690/697 and730/743/750 are the two short-circuit
rejection branches, respectively leaf32,field32,bytes64. Common exit/drop ID808
is bytes64, including success/normal OS-error exit. Branch paths are retained;
counting syntactic sites alone is not an exactly-once or order proof. Source
return constructs move the two32 owners. Returned type glue31 has normal field1
then field2 drops and an unwind field2 path, without dropping the public nonce.

These sites target Zeroizing glue36 specialized to the concrete32/64 arrays.
Glue36 calls the unchanged Drop implementation59 and also contains projected
trait-drop of its inner generic Z. Drop59 calls array Zeroize through its
trait dictionary; array9 uses slice/iterator Zeroize26, then each byte uses
blanket10, volatile_write27 and atomic_fence28. The actual instantiated u8/array
inner drop is trivial; that source fact has not been substituted into an
accepted mechanized glue evaluator here. Function143 is opaque Iterator::next
returning Option<&mut T>;159 is opaque trait Drop. This is a generic graph,
not a new concrete-only monomorphized graph. It does not meet candidate014's
supported shape. No backend experiment or trust grant is justified by merely
printing these operations, and candidate015 remains unaccepted.

Prior native-owned-drop Kani045/046 covers actual array Zeroize32/64;
049/050 covers moved-owner, retained-storage actual destructor and untouched
frame. Compare exact zeroize1.8.1 source hashes in their receipts to this job's
preflight; same unchanged implementation. Initial047/048 child-pointer evidence
is superseded for lifetime reasoning. The source chain and specialization map
identify which leaf relation applies, under existing sequential Kani/P6 semantics.
They do NOT prove the factory invokes that relation with an event count/order
or that an error/return trace transports it. This is an explicit open producer,
not an opaque cleanup axiom or an assumption hiding whole-output equality.

To close it, produce a supported concrete glue/caller evaluation, or a reviewed
source/MIR instrumentation contract that emits before/after events around the
REAL invoked destructor and proves instrumentation erasure plus admissibility.
A logger replacing Drop is not sufficient. Unwind/abort cleanup, arbitrary
capture/loan boundaries and old moved storage remain outside these checks.

All existing theorem statements and premises before/after are identical. No
kernel theorem or new trust assumption is introduced; #print axioms is N/A.
