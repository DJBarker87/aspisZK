Target not yet established.

LIBC-F01: L001/L002 broad diagnostic imports reached missing historical RawTx1DigestLog. That import shape is retired; use focused imports or privately compile missing unchanged dependencies. No proved fields or rows resulted.

LIBC-F02: L004 used stale rev2 RSL_specs ahead of rebuilt rev3 RSL objects copied in LIBC_base. Own PATHS order corrected to select pinned rev3 base objects first. L005 diagnoses the old ordering and is not a field. RSL.Byte is not a canonical type: corrected own source to UInt8.

LIBC-F03: L028 output_length hit recursion depth while elaborating a concrete List.ofFn length through placeholders. Replaced with a symbolic bytes_ofFn_length lemma parameterized by n and applied at13831; no recursion/heartbeat option increased. L028 is excluded.

LIBC-F04: L032 original NBL_CohortCode import conflicts with canonical RPz7_PreparedFromQmSourceBridge owner. Original import excluded. PreparedLog now constructs the same fixed code from RPz7_S1ClosedPreparationHashCodeV1; dictionary identity is proved explicitly, no owner stand-in.
