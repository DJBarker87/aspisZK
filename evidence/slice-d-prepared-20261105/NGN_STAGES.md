# Frozen Prepared::new stage cuts

Frozen body and source correspondence: NFW_PREPARED_NATIVE_SOURCE.json, hashed in NGN_REUSE.json. No whole-function native harness is used. Source lines below are the frozen verifier.rs lines, not inventory IDs.

| Cut | Source operation | Same live variables entering next cut | Native status |
|---|---|---|---|
| S0 | L73 SemanticTranscript::state; Transcript::new | sem, view, hash, transcript state/hash, old scratch | NFW seed/state fragments reused; full arbitrary-byte runtime association OPEN |
| S1 | L74 scalar(27,y1,true) | returned gamma and transcript, original sem/view/hash/scratch | NGN gamma stage: argument byte/length/mode, reply/state, hash/live-locals frame |
| S2 | L75 inactive bytes; scalar(28,bytes,false) | same gamma, returned kappa/transcript | NGN kappa stage; actual native serialization executes |
| S3 | L76 scalar(29,round0,false) | same gamma/kappa; returned alpha0/transcript | NGN alpha0 stage |
| S4 | L77–82 folds/payload/optional scalar30 | same gamma/kappa; alpha pair, row30/31 and transcript | NFW_K069/K070, K099/K100 reused, not replayed |
| S5 | L83 queries(row,final_message)? | success: same opening, query array and transcript; error: old scratch | NFW control fragments reused; new suffix cut association pending |
| S6 | L84 scalar_k(row+1,empty) | same opening/queries; returned rho/transcript | NGN rho stage |
| S7 | L86 scratch=powers29(gamma) | same gamma/kappa/opening/queries/rho; SAME overwritten scratch | NFW powers packet reused; whole-assignment association pending |
| S8 | L87 prepared_claim(sem,y1,inactive,scratch,kappa)? | error retains overwritten scratch; success SAME claim and prior values | NFW call fragments + KNF/LPt leaf reused; full semantic/byte-domain installation OPEN |
| S9 | L88 final record/Box | eleven result fields; current scratch | NFW_K065/K066 + field-copy controls reused; new predecessor link pending |

Native stage oracles overapproximate replies; a passing local cut is not a callee semantic law. NGN_STUBS.md distinguishes installed laws from OPEN pairings. NGN_Cuts/NGN_Opening factor the model's exact Result computation. These facts do not by themselves certify native execution or close TX1:179.
