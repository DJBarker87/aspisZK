# Rejected attempts and replacements

- NCB_K001: EXPECTED negative control failure, exact b[15]==0 false assertion,1/20 failed. Successful mitigation control, no implementation failure.
- NCB_K003: u32 one-resize-step with symbolic old length0..1 TIMEOUT,90s solver bound; no native credit. Split fixed lengths and selected postconditions next; no cap/timeout increase. Owned solver temps cleaned separately.
- NCB_L002: failed model instance elaboration: unrestricted simp reduced the concrete14759 replicate inside its bound. Replaced by simp only [List.length_replicate], preserving the statement and avoiding evaluation. Its printed sorryAx reflects elaboration failure, never accepted evidence.
