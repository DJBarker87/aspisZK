# Findings

NLZ-F1: K001 stopped before Kani verification because the own configuration omitted PATH for rustc. Frozen graph check passed, post-run lock unchanged. Corrected to predecessor PATH and optimized flags at K003; same harness name. This is an own-input repair under local-lean11, not a shared-infrastructure failure or a renamed verdict.

L003/L007 syntax errors in the new resource carrier are retained; no timeout or memory kill, no limit raised.
