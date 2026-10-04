# R569 provenance correction

This note is separate from the immutable R569 capture/translation receipts.

The `source_revision` value `4f2f2f13a55425cedb2cdc19cfcf2780edbb8b35` copied into the early prelaunch receipt is stale campaign provenance, not the current repository HEAD. The current campaign HEAD is `95261201338bfba305516455f07bfb55d014f17d`; the frozen selected-source baseline remains revision `6677d5f1310ff7373301fbd79f186278f772e68a`.

The selected frozen `aspis-core` source used by this capture is unchanged from that freeze. The isolated R569 stage does include one host-only extraction wrapper appended to `relation_callback.rs`: `claim_probe`, which calls the selected `begin_state_only_masked_sumcheck` function. Therefore the accurate statement is “selected core source unchanged; isolated stage adds a dead capture-only host root,” not “the entire stage has no source delta.” The wrapper does not modify the selected verifier or its callback.

The early receipt is retained byte-for-byte; this note corrects its interpretation without rewriting historical evidence.
