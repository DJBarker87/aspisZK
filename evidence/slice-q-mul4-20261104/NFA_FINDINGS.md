# NFA findings

Audit interface: unchanged NEP_Driver hard-codes non-NEV roots. The NEP_WALKER traversal will remain byte-identical; permission to adapt only driver root/module lists is pending. No strengthened audit pass claimed yet.

NFA_L047: strengthened runtime audit of NEV_DotResult failed at the fixed -M7000 threshold (excessive memory consumption in interpreter). No roots in that group earned credit. No unchanged rerun or cap increase permitted. Receipt NFA_L047/receipt.json and stdout retain the exact failure. Isolate a root / reduce driver startup retention before another attempt. Other module groups continue independently.

NFA_L049: the separate NEV_ActualDotStep group hit the same import/interpreter memory boundary before a reachable graph artifact was produced. Stop interpreted full-caller groups; replace startup mechanism with a compiled runtime driver, without changing the walker. No failed group earns credit.

NFA_L065 excluded: resource API required explicit Lean.Shell import. L066 linked the prior L063 C artifact, so this binary is EXCLUDED (not executed), and will be replaced from a successful fresh source compile. Own script sequencing corrected; no host infrastructure changed.

L067 excluded: Lean.Shell resource API is private in the Lean4 module system; requires import all Lean.Shell. L068 again linked the old C artifact and is excluded without execution. Dependent linking is now gated on the preceding compile result, not merely process completion.

Peer replay own-view repairs: materialized missing tracked baseline validator directories using sparse-checkout add. Corrected GIT_WORK_TREE from realR to private validation root S so git ls-tree paths are rooted correctly; strict provenance checks unchanged. Final unchanged NEW_validate replay passes at revision75623b7b43c563b210f2f37d74182382569f7002; no writes to predecessors.

NFA_K009 matched no harness because own selector omitted KMX_checks. Corrected selector K010/K011 gives required pass/fail; original failed selector preserved. No renamed proof or verdict-seeking source rename.

NFA_K018: full selected-tail window strengthening timed out, exit 124, wall 180.15594435017556s, RSS 100380KiB, swaps 0. No credit, no matched negative launched, no unchanged rerun. Split physical source-pointer/one-byte window from opaque receiver context; existing native K005/K006 isolates coefficient value read and inherited NEV_K066/K067 isolates receiver/call context. Full composition remains a Lean obligation.
