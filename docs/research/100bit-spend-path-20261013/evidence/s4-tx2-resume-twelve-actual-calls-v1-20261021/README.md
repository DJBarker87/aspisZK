# S4 tx2 resume guard to actual twelve-call fields

`resume_model_candidate_twelve_actual_fields` binds the selected Stage2 `resumeWithOps` model to the tx2 prefix. From one successful prefix result, it recovers the resumed `(Prepared, Accumulator)`, derives `a.next.val = 10` from the split guard, obtains the same powers array used by the query loop, and applies the checked candidate-loop theorem to expose twelve actual candidate call successes and their scanned field evidence.

The upstream authenticated/prepare contracts remain explicit: `ResumeOps`, strict scan success, and canonical prepared gamma. The result is scoped to the selected continuation prefix and is not a proof of whole `tx2_common`/`tx2_authenticated` Rust correspondence. The existing P6 and query-operation source boundaries remain as documented in their producer packets.
