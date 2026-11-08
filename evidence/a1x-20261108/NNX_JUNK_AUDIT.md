# X0 evaluator audit

The only explicit panic value in 345/328/094/087/136/137 is 345's `.ok []`
on account patterns other than exactly three. NNX_JunkAudit proves those
inputs take the earlier badRoute error. No replacement evaluator is needed.

328: first_returned uses call; its 094 domain on the reached 345 path is
NNV_DecodeP1880.returned (reused, not reproved).
094: prepare call_domain is the 087 domain from that SAME root. All other
children use their explicit library value, not a fresh panic choice. Missing
folded-root toB32 is explicitly `.error V.vParse`.
087: front semantic call_domain and prepared call_domain use explicit child
values; their domains still need caller derivation in X3/X4. They introduce
no chosen `.ok` fallback. This audit does not claim those domains proved.
137: finish call_domain uses NNH_FinishReturns.value; its domain is still part
of X3. No panic or free chosen fallback in the evaluator.
136: missing root conversion is explicitly `.error V.wPublic`; all other
checks use explicit Except results and library children.

Off-domain call sites remain proof obligations at the exact reached inputs.
`call_domain` makes Returns vacuous off-domain; an explicit evaluator alone
does not discharge native/model correspondence. X3/X4/X7 must derive their
domains or prove the full Result equality there. No field is delivered.
