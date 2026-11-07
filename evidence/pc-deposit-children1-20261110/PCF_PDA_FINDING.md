# PCF-F1: native PDA opaque-call association remains OPEN

POOL:280 needs an exact request and unchanged reply/bump bridge for the owner-approved quantified op38 slot, not a PDA value. Its frozen body builds exactly three seed slices: `aspis-pool-root-page-v1`, the SAME pool bytes, and page_number LE8, then tail-returns `Pubkey::find_program_address` at the SAME program id.

The SDK function's read-only slice/program signature does not carry the local mutable request/reply record needed by the existing (y)/(ak) logging route. A deterministic pure opaque-function family was tested as a possible alternative without writable statics or a PDA value law. PCF_K023 (repeat same u8 query) and PCF_K024 (unimplied different-query equality) both fail on Kani's **unsupported foreign C function** check for `__CPROVER_uninterpreted_PCF_u8`. Neither is a semantic negative control or a passing interface calibration. No such family is admitted, no Kani/backend/shim/library patch is made, and no PDA value or new runtime trust row is introduced.

A fixed reply, reply tied to one input, successful SDK outcome, unobserved pointer context, or hand-built typed result would not establish the required universal reply/argument/frame law. These are not used as closure evidence. Static tail-return/source inspection alone is not promoted to the required native certificate.

Next: a supported local-record SDK/op38 request/reply bridge, with exact ordered byte slices, program id, status/output-region and bump forwarding, modifies/frame, matched corruption control, and abort prefix. Then consume that bridge at this row's actual arguments and finish the NCO reference/model law. This one interface finding also applies to dependent PDA uses in OPEN304; it is not duplicated as multiple wrappers.

Current status: POOL:280 OPEN; no native or row credit from K023/K024. Other independent work continues.
