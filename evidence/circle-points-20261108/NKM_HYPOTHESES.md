# Root hypothesis inventory against (aq)(2)

NKM_Review.lean prints the full selected roots in the combined environment; its scope stdout is the statement receipt. NKM_Roots also prints circle/ood/fallback at the focused target.

|Authoritative local root|Quantifiers / hypotheses|Disposition|
|---|---|---|
|NKM_Roots.circle; NKM_CircleModel.circle_source|t : QM31Exact, no Prop hypothesis|Input parameter ranges over the full exact field, including both poles; encoded canonical domain covers every caller input by roundtrip|
|NKM_Roots.ood; NKM_Adopted.ood|t : QM31Exact, no Prop hypothesis|Both rejection arms and singular-first order are conclusions; no denominator/non-subfield premise|
|NKM_Roots.fallback; NKM_Adopted.fallback|the two-case deployed CircleRow enum, no Prop hypothesis|Caller constructs sample 0/1 exactly; fixed parameter inverse certificates and c1≠0 are proved internally|
|NKM_Trace.complete; NKM_OuterTrace.complete; NKM_FallbackTrace.complete|field input or row enum, no Prop hypothesis|Full returned record and chronological field-call trace; fallback error-arm flag is proved false|

circle_on_canonical/ood_on_canonical are convenience transports with Canon as the explicit input domain. They are not new release premises: NKM_Domains.caller_sample derives it from the same sampled block, ood forwards the same parameter, and fallback_domains proves it for both constants. singular/regular lemmas use a branch guard solely inside a total case split.

The only native assumptions are the reviewed per-call source-cut transcriptions, existing CLOSED callee contracts and their caller-established domains, exact KMX copies, and accepted P6/D188 semantic transport. These are the allowed (ai)(5)/(aq)(2) cut inputs, not an extra endpoint equality. Every child Result and domain is instantiated inside the concrete emitted-body proof. No caller acceptance, independent successful execution, output equality, log-association premise, arbitrary Ops dictionary, allocator outcome, NIG finish domain, extra runtime row or cryptographic premise is added.

Headline hypotheses, L154 statement parameter, approved runtime trust rows, per-attempt 100-bit target, privacy and two-transaction game remain unchanged. RuntimeCpiReadonlyEntry7 is unused. These local roots do not instantiate the enclosing AeneasExtraction premise for the entire deployed verifier.
