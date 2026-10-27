# Persistent source-upload transport failure

Mandatory stop under local-lean.txt rules10 and5. Rule10 says “Only a persistent failure (3 consecutive) is a rule-5 stop.” Rule5 says “If the launcher or host misbehaves, stop and report the exact error ... the lead fixes infrastructure. Proof work only.”

The initial source upload for XSb_L001 returned255, then two retries of that SAME scp transport step after30 seconds each returned255. All three printed exactly `scp: Connection closed`. See XSb_transport_retry1.log, XSb_transport_retry2.log and XSb_transport_events.json. The original Python invocation raised CalledProcessError at line24, source scp, before configuration upload/systemd-run/Lean. The admission was allowed:true AND exit0; this is not a reservation refusal or a timed-out/memory-killed Lean run. No launcher repair, protocol substitution, admission bypass or further host launch followed the persistent failure.

Exact failed operation:
`scp -q evidence/extraction-assoc20-20261027/XSb_PredecessorAudit.lean dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-assoc-a6-cache-20261027/XSb_generated/XSb_PredecessorAudit.lean`

No compiler process started. Budget compiler0/100,Kani0/10; one admitted precompiler attempt slot reserved, conservatively1/100 slots if preflights count. Budget is NOT exhausted. Full-budget instruction cannot override the explicit persistent-infrastructure stop. No scope started; actual wall/RSS/swap/axioms for XSb_L001 are null (not zero measurements). No final co-import/root replay, full manifest or final END cache snapshot. The recovered102-object snapshot precedes the failed uploads and is labelled START/recovered only. Persistent cache and any upload partial retained; no cache/key deletion, no own compiler/Rust/Kani process launched.

Retry logs normalize terminal CRLF to LF; diagnostic text is unchanged. Final local statement-hash comparison passed; all79 selected prior cache objects match. No host action followed stop.
