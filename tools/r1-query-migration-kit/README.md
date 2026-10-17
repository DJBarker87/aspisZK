Native test-only Decision1e/1f gate; no production candidate edits. `prepare.py --after FINALREF --stage SNAPSHOT` appends the exact old query method and a test module to the current actual transcript source. The sole method-body adapter, applied symmetrically, redirects the pure decoder to a test wrapper that normally calls the actual implementation. Current `queries` and actual `Transcript`/absorb/field embedding/prover trace run directly.

The digest interface is infallible. Abort tests panic with the selected position and catch that exact payload; they establish abort/input/trace-prefix agreement and do not claim a ProgramError. Altered-answer tests compute actual SHA256 then flip one bit in one selected answer and retain the real returnedResult. An unused pair may remainOk. DecoderErr is an explicit test-only boundary error. Each real/synthetic context includes16abort positions,16altered positions,decoderErr,success (34cases); threecontexts yield102. All complete hash slice boundaries/answers, decoder inputs/result, errors/abort payload, receiverstate and22trace values/order compare exactly. Successchecks state against the actual decoder returnedstate, without assuming the eighth advance was selected.

SavedS2 state/payload and17exact expectedcalls come from the actual accepted saved-proof583-call run at1b98, orderedindex95; its original proof/public fixture hashes and full counter evidence are retained in that native workspace. The old/new source changes afterward affect only semantic helper factoring, so the query method/context stays byte pinned. SyntheticS1/D contexts exercise row30/31 control flow with real SHA/core arithmetic but are not claimed validproofs. Query has no variant argument; those labels describe schedule contexts only.

Target (capped host only):

```
cargo test --release --locked --offline -j1 -p aspis-r1-cost-probe --features prover,private-leaf-salts,optimized-terminal --lib transcript::query_migration_tests::queries_exact_old_new_all_digest_positions_and_decoder -- --nocapture --test-threads=1
```

No SBF, proof generation or runtime harness. This source-only kit is not a passing gate until the child receipt/logs are recorded.
