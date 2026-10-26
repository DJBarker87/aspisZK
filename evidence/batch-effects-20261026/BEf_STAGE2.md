# Stateful interpreter rules and native witness preflight

Checked BEf_Fold.carrier reconstructs the complete carrier from the actual
attempted suffix, including a failed final call. BEf_Bind.run preserves that
carrier/log through sequential failure. BEf_Relation.simulate transports
related carriers under a local syscall simulation. These are generic proof
rules; no native carrier instance is assumed or claimed. L166 stays open.
BEf_007/009/010 passed; 008 failed elaboration and is excluded. Standard axioms
only in successful receipts, zero swaps, verified 6G/8G/Swap0/Tasks64 scopes.

BEf_extract.py --check validates ten complete, verbatim candidate.rs function
items in BEf_native/src/BEf_source.rs. The standalone crate links the unchanged
native multiproof and private-leaf implementations, with real sha2 SHA-256.
It changes no shipped source or cfg(kani) module. Neither SHA nor any batch
child is stubbed. BEf_R001 optimized Rust: both direct batch fixtures reject
nonzero padding with Err(Parse), exit0,44.375862s,592396KiB,swap0.
The fixture is a direct malformed batch invocation, not a complete accepted
SDK transaction. It extends the existing local Port4B rejection diagnosis to
reachable complete native batch calls, but does not establish a complete
Lean evaluation of those physical fixtures.

BEf_K001 failed on reachable SHA CPU-detection inline assembly, not an
assertion counterexample: exit1,31.908363s,531680KiB,swap0. Its undetermined
checks receive no credit. K002 replaces the unsupported hardware-selection
path with sha2's real force-soft implementation; no cap increase or stub.
Native source, dependency hashes, commands, exact target/revision, all metrics
and output are retained in numbered receipts. No ELF rebuild trigger or
release claim. Other prefix/worktree/key files remain untouched.
