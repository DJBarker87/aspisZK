# P3 literal host call-slot table

Target not yet established. S3 L730–747, standard axioms for accepted roots.

| Reached slot | Status | Evidence / exact gap |
|---|---|---|
| op0 Option conversion | unchecked pointwise | Port1_Library.std supplies okOr |
| op2 inactive | OPEN additional slot | Port1_LibrarySource.decode vs NJC_ClosedCalls.inactive |
| op3 authenticated parser | existing prefix support, no fresh transport | Tx2I_Install.shape vs NLE_ParseInstall.parse |
| op5 Merkle | OPEN | Port4B_Install.batch vs NLP_NativeMerkle.action; node/leaf oracle values PASS L745 |
| op6 query | OPEN | Actual SAQ/FIp query installation vs NJJ_Common.query at resumed invariant |
| op9 flush | rfl PASS | NNH_Tx2LiteralSlots.flush L742 |
| op10 pending | rfl PASS | NNH_Tx2LiteralSlots.pending L742 |
| op11 geometry | OPEN | Actual twice-installed SAQ_Constructor geometry vs adopted |
| op13 mark | rfl PASS | NNH_Tx2LiteralSlots.mark L742 |
| op14/15/16/20/21/22/23 | literal values PASS | L742; canonical NHT computed-constant normalization OPEN |
| op17 powers | rfl PASS at Tx2N_Powers | L742; canonical native powers association still needed in converse |
| op18 reader | existing returned-path support | NNH_AuthResumeSdk/NNH_Stage2ResumeOccurrence; no fresh rev4 claim |
| op19 finish | full pointwise PASS | NNH_ResultPortTransport.finish L738 |
| unwrap32 | unchecked pointwise | AuS1 installs Port4B_FoldedCut.unwrap32 |

Only the Ok direction is required. No whole-dictionary congruence or new final premise.
