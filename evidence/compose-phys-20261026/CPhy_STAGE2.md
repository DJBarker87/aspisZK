# Stage 2: physical premises derived inside joint top

Checked endpoint: CPhy_Physical.accepted_pair_unified (CPhy_010).

Before: CPhy_Accepted's caller continuation quantifies arbitrary decode,
nodes and y1 and takes writer.header/size, reader.checkedHeader,
both batches' PhysicalRange fields and scan Y1Range as premises.
After: the same accepted pair, SourceCuts and Tx1Q Run produce these joins
as unconditional conjuncts. The continuation uses the concrete digest-field
decoder CPhy_Header.decode, installed nodeSlot buffers CPhy_Ranges.nodes,
and canonical_scan's compact input CPhy_Ranges.y1; it no longer takes the
writer, reader, multiproof or scan joins as inputs. All other conclusions,
including native writer success and the conditional Tx2N Outcome, persist.

This is explicit instantiation of formerly arbitrary observation witnesses,
not a theorem about every independently chosen decoder/node/y1. No runtime
or cryptographic inputs, result/failure events or security metric change.
The semantic wide-view expanded y1 remains separate from compact scan y1.
The retained arbitrary-observation theorem remains available in CPhy_Accepted.

The source route uses symbolic proof/public digest cells in the selector
body, the same returned saved Vec and actual digest calls; native writer
association is retained through stage 1. Reader resume comes from the
joint top's actual second-stage call and concrete byte-comparison callbacks.
S2W_DigestExtraction.native_oracle supplies only the returning-call law.
No total syscall success or independent successful reader is assumed.
Both proof lengths come from actual installed header success. Each node is
the result of the installed Port4B_Install.leaves.op3 on that batch's actual
proof; CPhy_Ranges.physical proves that equality and all four range fields.
CPhy_Ranges.scan inverts installed Op4P source success and returns BOTH the
checked range and check_values success on the identical compact y1.

Ledger delta for this actual-source observation endpoint:
REMOVED L091, L092, L093, L100, L101, L102, L103, L104, L105, L106, L107,
L108, L109. Stage 1 already removed L171-remainder/composition.
ADDED: none. Full L171's retained arithmetic/domain/WhenBound obligations
are not claimed removed. The global ledger is untouched under prefix-only
ownership. No other-cone or global security premise is claimed discharged.

CPhy_010 exit0, wall3.163868s, peakRSS5254380KiB, swap0,
revision666092089d plus exact dirty source snapshot/hash. Axioms exactly
[propext, Classical.choice, Quot.sound]. Focused dependencies CPhy_002,
005 and007 passed. Failed003/004/006/008/009 are retained diagnostics,
never proof evidence. No timeout, memory kill or cap change. Budget10/100
Lean submissions,0/30 Kani; no dependency rebuild was needed.

Non-vacuity: the joins are derived before any runtime retention/P2Prime/
FirstEntry premise. They add no acceptance restriction. The source helpers
are total checked ranges at actual admitted lengths; scan acceptance yields
its own successful check_values call. Existing local WAdm and SdkD witnesses
retain their stated scope. A jointly inhabited cryptographic/runtime accepted
pair is not newly asserted. S2 and the 100-bit release target remain open.
