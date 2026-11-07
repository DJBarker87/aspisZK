# NMC findings and credit boundaries

Target not yet established. No row promotion.

1. The initial draft rest heap stored Claims values only. That was insufficient for arbitrary other allocations and metadata. It was replaced by arbitrary raw regions (base, extent, alignment and per-byte initializedness) plus fully initialized typed Claims regions; all affected own objects were rebuilt. The discarded draft never earned physical closure.

2. The native helpers return local Unit/selected-value frontiers while retaining a borrowed parent. They are components of source-ordered cuts, not the frozen function's full Result<Verified<SolanaDigest>,Error> exit. In particular they do NOT establish the actual error-exit cleanup/allocator/rest-heap chain or full returned-record ABI. The required terminalGuard/circleGuard/mapPublic segment contracts remain OPEN. No contract-interface or returned-record fidelity credit is claimed from these plain Kani windows.

3. Native Parent fields are the persistent local projections plus explicit observations. Original Prefix/Public inputs, partial-initialization destination regions, the current allocator outcome, and the correspondence of the observed Box to the ONE source allocation still need same-state realization in the enclosing context. Passing a pointer comparison never supplies data or freshness. The full context contract quantifies every heap region and original argument; the partial native windows are not asserted to prove it.

4. Full terminal-entry positive/control K039/K040 both timed out. No receiver/argument/full-Result or matched-control credit follows. A future budget must split receiver identity, claims/alpha/original challenge arguments, reply, and arbitrary-offset full frame. No SHA or field multiplication was reached. K038 decode26 is positive-only and receives no native credit.

5. NLU's old input-row table marks256 OPEN. This is historical: ledger23 admits Actual256 as CLOSED, and NMC_PINNED_CHILDREN.json pins that authority. NMC uses NLU_Terminal.nativeTerminal/installed and NLH's actual full-Result transport, never NLI's provisional256 interface. The mask is row076; row147 is decode_k.

6. Source occurrence frames, stored-value provenance, full-effect contract statements and generic forward reassembly are Lean support. None is a concrete native136 execution certificate. No missing refinement is reclassified as a cryptographic assumption, no security metric changes, and no new runtime trust row is introduced.
