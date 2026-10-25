# Stage 3: N116 removed without restricting transcripts

T2R_Pair.accepted composes directly on the same predecessor f,s/run/tx2.
T2R_Ten.Outcome deletes ONLY ten.parseReached. The actual source run is
passed to Tx1Q_Model.ten using the selected authParsed.wire identity obtained
outside the continuation from its original source parser. All tr,q,data,rho
quantifiers and preparation/read/geometry laws stay unchanged. Collision and
success conclusions stay unchanged. This is stronger for every transcript;
no constructed/honest-only transcript, Aligned guard or hidden parser law is
substituted. The source-authenticated recovery callback is the original
AuS1_OnRun callback, at the same frame and accepted pair. No PSem/PAln replay
was needed for this removal: inspection isolated the truly used wire fact.

T2R_Top.deployed now returns T2R_ResultSource.Outcome. Removed actual families:
L085-L087, L122-L124, L126, N116 (8). Added: none. entry.parsed L099 remains.
Structural carrier L151-L153 qualifications in Stage2 remain unchanged.

T2R_013-018 all pass, including exact top T2R_018: exit0,1.991001243s,
5280268KiB RSS,swap0,revision9f143a1de1 dirty exact source snapshot in receipt.
T2R_Pair.accepted and T2R_Top.deployed audit standard axioms only. Four
intermediate targets are definitions only, no new theorem axioms to audit.
18/80 Lean,0 Kani. No timeout/OOM/cap changes/shipped changes. No release claim.

Remaining budget will investigate exact source semantic/public association,
not count an independent Par existential as the shared Cons witness. The
recorded dependency plan is a read-only inventory, not a build/replay result.
