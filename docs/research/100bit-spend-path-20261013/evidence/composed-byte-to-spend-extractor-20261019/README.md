# Composed actual finite-byte extractor to a checked spend witness

The fixed-log executable extraction chain is now connected:

1. Ordinary runtime array constructors normalize the fixed received words at literal deployed initial/final points. Their equality to the mathematical normalized arrays is proved.
2. The maintained concrete byte sampler feeds the actual 29-initial +5-final GS interpolation/root-recovery bank.
3. Success of actual initial root calls supplies interpolation witnesses and complete root lists; no caller-supplied hQ/Candidates contract is assumed by the new composed theorem.
4. Actual image/distance filters feed the ordinary joint-list merge, followed by the retained checked spend-witness scanner.

`GSByteJointSpendExtractor.extract` is an ordinary executable definition. `returned_valid` proves that every returned witness satisfies the current AppendBinding-aware `Rspend` relation, for every input and coin tape. `decodedLists_complete` derives per-lane mathematical Close inclusion from the actual sampled bank output outside its observed rejection/abort event.

`GSByteJointSpendExtractorCompleteness.failure_mass_small` proves that this exact composed executable function returns none with probability strictly below 2^-126, over the actual finite raw-word coin space. All public/received words and transcript/semantic data are fixed before the mean over private coins. The theorem assumes the existing successful public/matching/opening readers, no classifier hit, Good/accepted matching/support, semantic parse/check equations and typed-word equality. It no longer assumes an external random-field oracle, sampler law, field cardinal/oddness, interpolation witness, root completeness, per-lane decoder completeness or candidate-list-to-set equality. The modeled semantic/no-hit conditions remain material hypotheses and are not established from deployed verifier acceptance here.

The final five input words are fixed caller inputs. Their full four-channel second-fold source/repetition/projection correspondence remains a separate obligation. The algorithm uses the initial bank results to construct the witness; all five final bank calls are included in the conservative bank abort bound.

All five new focused native Lean 4.32 targets passed under finite 6 GiB cgroup caps, MemorySwapMax=0 and fresh host admission; every printed axiom report contains only standard axioms. Exact source/import/object pins, commands, source revisions, GNU maximum RSS, wall/resource records and reusable native objects are retained. Existing source-identical dependencies missing native evidence were compiled only in this caller's selected closure (the byte sampler/GS native owners); no package-wide or complete frozen-manifest replay was run. Structural array/function equalities were proved before field arithmetic; failed initial attempts that tried implicit array unification were replaced by explicit symbolic rewrites and opaque runtime points, rather than raised resource limits.

This is a fixed-log extractor theorem, NOT the full 100-bit spend result. Remaining: accepted source executions imply the modeled checks; canonical completed-log commitment-word recovery and freshness coupling; classifier-hit/ROM/collision bounds for the actual unrestricted-byte accepted execution; full implementation-linked operation/bit costs; source/runtime/artifact preservation; privacy and the one-or-two verification/settlement transaction gates. No grinding or work credit is used in this extractor failure bound.
