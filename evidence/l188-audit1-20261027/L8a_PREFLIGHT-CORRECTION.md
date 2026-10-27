# Corrected job input before compilation

The initial prefix-only receipt-adapter copy incorrectly changed RPz8_overlay to L8a_overlay in the default LEAN_PATH. Dependency pin preflight rejected RPz8_Rc10_Top before writing a launch config or invoking Lean. Restored the unchanged RPz8 cohort path; no launcher, monitor or shared object changed. This is zero Lean compile attempts and no failed proof rerun. Initial admission receipt is retained; the next admission is fresh.

The first replacement failed to match the literal colon; second dependency preflight also stopped before Lean. L8a_001 and L8a_002 are admission/preflight-only IDs, not compiler attempts. L8a_003 is the first compiler request.
