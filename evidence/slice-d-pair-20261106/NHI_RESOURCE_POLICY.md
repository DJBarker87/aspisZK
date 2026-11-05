# Scope admission

The JOB section specifically permits up to TWO concurrent capped scopes under admission, overriding the general one-scope default for this job. Native attempts remain sequential in one scope; one independent focused Lean/audit scope may overlap. Both require allowed:true AND exit0 admission, each 6G/8G/swap0/Tasks64. No third scope is allowed. No raised caps or timeout.

Budget accounting correction: L033/L060 failed while pinning missing prerequisites, before submission; no Lean process ran. The own runner now enforces 90 actual L receipts (all Lean/link/audit scopes), not numerical identifier<=90. L091/L092 can therefore consume the two unused slots without raising any budget or resource cap. Kani still has exactly120 receipts, including its compile failure. NHI_PREFLIGHT_FAILURES.json is separate; every actual scope remains charged, including failures.
