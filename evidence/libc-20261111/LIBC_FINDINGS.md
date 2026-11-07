Target not yet established.

LIBC-F01: L001/L002 broad diagnostic imports reached missing historical RawTx1DigestLog. That import shape is retired; use focused imports or privately compile missing unchanged dependencies. No proved fields or rows resulted.

LIBC-F02: L004 used stale rev2 RSL_specs ahead of rebuilt rev3 RSL objects copied in LIBC_base. Own PATHS order corrected to select pinned rev3 base objects first. L005 diagnoses the old ordering and is not a field. RSL.Byte is not a canonical type: corrected own source to UInt8.

LIBC-F03: L028 output_length hit recursion depth while elaborating a concrete List.ofFn length through placeholders. Replaced with a symbolic bytes_ofFn_length lemma parameterized by n and applied at13831; no recursion/heartbeat option increased. L028 is excluded.

LIBC-F04: L032 original NBL_CohortCode import conflicts with canonical RPz7_PreparedFromQmSourceBridge owner. Original import excluded. PreparedLog now constructs the same fixed code from RPz7_S1ClosedPreparationHashCodeV1; dictionary identity is proved explicitly, no owner stand-in.

LIBC-F05: L039/L040 numerical Usize capacity equality failed under rfl/scalar_tac. That numerical normalization shape is retired. Reuse the CLOSED NGN_RowArithmetic.capacity symbolic wrapping/checked equality to prove only the needed existence of a successful capacity result; no cap/timeout/options change.

LIBC-F06: Direct import of NMT_R2_ConcreteS1/ReachLibrary brings NMT_RSL_Base, a second owner of RSL declarations; L068/L069 cannot coexist with canonical RSL_Base. Those imports are retired. LIBC_S1 uses the same literal concrete leaf operations and the canonical RSL_TX1_345 type, reusing NMT_345 leaf theorems and the ReachFull source contexts read-only. The missing NMT_tx1 objects were copied from the retained NMT export with hashes in LIBC_NMT_PINS.json.

LIBC-F07: NLL's adopted History stores flattened inputs. Treating those lists as singleton digest partitions would change the RSL event. LIBC_HashPartitions proves a lossless inverse for the exact native node/leaf address families; LIBC_HashShapes proves each source family has that shape. LIBC_CohortHash then constructs the fixed Env backend without assuming Env.sha256 is partition-extensional. No new digest-totality or SHA trust item is asserted.

LIBC-F08: Raw ax2 group1 found no object for LIBC_HashShapes.leaf because that standalone backend-family lemma was not imported by the initial field-group combined module. All39 found roots were standard-only with matching collector; the scope still fails and is not credited. The own combined import is expanded to include every accepted own theorem module (including PreparedErrors). Recompile that changed import, then re-establish the rejected group against its changed closure and audit the remaining groups. The repeated group is specifically the missing-object evidence question; group0 is not repeated.
