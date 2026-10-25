# Op4 whole scan installation preflight

Branch codex/cx-op4-install-20261025. Read root AGENTS Security and proof discipline,
common/local rules, historical S2 handoff/plan/diagnosis/interface, C3-BIN route B
adoption, and SInt2 / RowShape handoffs. Historical paths resolve under
`docs/research/100bit-spend-path-20261013`.

Target: success-conditioned whole extracted canonical_scan installed ONLY in
CurrentCaller Ops.op4, on the same accepted_pair_claims execution. The frozen
nonsemantic predicate is OraclePortCompactDraft.scan, called by parse inside
OraclePortStoredParserC4.parseReached. No source/model changes or law hypotheses.
Retained current-children extraction makes this helper opaque; use the pinned
Charon/Aeneas route to expose its actual body. No closure claimed at this stage.

Before: arbitrary Ops.op4 success gives no scan law (RowShape padding witness).
Required after: fix ONLY op4 to the extracted body; identical remaining premises
and accepted execution imply scan on the same stored bytes, including all openings.
No assumptions discharged/added at preflight; no changed carrier or failure event.

Only Op4I_ new modules and this evidence directory will be written. No shipped
source, candidate or live worktree changed. No ELF rebuild trigger. Inherited
pins f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

Host preflight: coherent SInt2 workspace accessible; no populated build scopes
besides init.scope. Reuse pinned objects; one module per attempt, -M7000 and
MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64. Optimized Rust extraction.
Budget 0/60 Lean, 0/20 Kani. No formal result; exit/wall/RSS/swap/axioms N/A.
