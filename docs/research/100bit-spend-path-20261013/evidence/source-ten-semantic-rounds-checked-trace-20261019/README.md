# All ten semantic rounds preserve their source check facts

Successful execution of RoundModel.rounds now supplies the initial row-14 record/decode/index witnesses, followed by a CheckedRun covering precisely rounds 0 through 9 and records 15 through 24. Each linked step retains the same decoded polynomial, actual boundary result, source comparison result, boundary equality to its incoming claim, sampled challenge/transcript, alpha update and outgoing evaluation result. The before/after running claim, alpha array and transcript match between consecutive steps and the final result matches the actual helper output.

This reuses the original unrolled ten-call reachability proof and the previously checked single-step success theorem. The first changed attempt elaborated all ten step facts but could not infer the intermediate tuple states from their projections. The corrected proof supplies those tuples explicitly; it changes no algorithm and raises no resource cap.

The focused Lean 4.32 dependent bridge passed in 10.87 seconds, peak RSS 2,312,732,672 bytes and zero process swaps. Only propext, Classical.choice and Quot.sound occur. Exact source/object/import hashes, command and source revision are retained. There was no full manifest replay.

The decode/arithmetic Boundaries remain explicit. Concrete implementation correspondence, coefficient-to-polynomial interpretation and final terminal-equation transport into sumcheckChecksZ, whole-verifier acceptance, completed-log word correspondence, and final protocol/security composition remain open. This theorem does not claim complete Rust refinement or 100-bit soundness.
