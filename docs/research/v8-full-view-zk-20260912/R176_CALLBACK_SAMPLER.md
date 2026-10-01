# R176 actual selected callback sampler

The selected generated `sample` closure, dictionary and function are staged byte-identically in `AspisR156FullFreeze.FunsSample`. `R176CallbackSamplerExecution.sample_factored` proves it chooses the actual ordinary/nonzero sampler according to its flag, maps inner sampling exhaustion to callback `Error::Sampler`, and preserves advanced transcript state and every outer fail/div result.

`sample_exact` composes R170/R173 with the callback wrapper for every total H. It concerns result/error/state only. Its model reuses the existing sampler runs and retains their traces as bookkeeping; there is no theorem equating those traces with the actual callback’s oracle calls.

Both focused files compiled in the pinned capped cache. FunsSample: 1.06 seconds, peak RSS 2,526,304 KiB. R176: 1.49 seconds, peak RSS 3,706,508 KiB. Both have zero swaps. Complete axiom reports are in the [evidence manifest](evidence/r176-callback-sampler/manifest.json), with only foundational Lean axioms and the inherited opaque Aeneas formatting type. The initial failed proof’s source and log are retained.

Next: connect the selected circle sampler to the existing error-preserving schedule, then finish actual pair/freeze and callback/oracle chronology through rho. Standard-library fold/extend and full-freeze error-return extraction still need faithful proofs. Privacy and soundness remain open. Verifier source, CU evidence and all security parameters are unchanged; no CU or unchanged regression suite was rerun.
