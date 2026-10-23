# Continuation 3: oracle ruling

Before: `S2LeadInterface.S2CallerFacts.oracle` required
`forall input, D.digest hash input = ok (rawOracle H input)`, including unused
inputs. `S2W_ClosureAudit.facts_require_backend_returns` correctly showed the
resulting unrestricted returning obligation. That audit is historical.

After: `S2W_LeadInterface.S2CallerFacts.oracle` is exactly
`CheckpointBytes5Inputs.Oracle D hash H`, i.e. each successful digest returns
H of its flattened input. Failed calls reject; the field imposes no totality
on unused inputs. All other thirteen fields, parameters, site and account
carriers are unchanged, definitionally. The original module is preserved per
the new-module-only instruction; this prefixed restatement supersedes its
oracle requirement for this job.

`S2W_SuccessOracle.before_to_after` constructs the entire new record from the
old record on the SAME Inputs, D, H, stored/public/checkpoint bytes and parser.
`returned_raw` supplies raw digest equality at each successful call, using the
array/state roundtrip. `native_success_field` uses precisely NativeBinding,
RuntimeSyscall and P1Realization, with no returning-domain assumption.
`masked_success` retains the old nonreturn countermodel and proves that it
satisfies the revised successful-call law.

All consumers of S2CallerFacts are reproduced and checked:

- `checkpoint_binding`: exact same checkpoint binding conclusion.
- `compose`: exact same save/resume, node views, S7 progress/invariant conclusion.
- `y1_join`: exact same parser/scan conclusion.
- `multiproof_join`: exact same both-batch conclusion and parameters. Its existing
  P6Boundary ALREADY contains its own total oracle law. The revised proof uses
  that child boundary directly, rather than replacing its oracle by facts.oracle.
  This does not discharge or weaken the multiproof child's P6 totality premise.
  An accepted-call-only P6 child theorem is still needed to remove that separate
  totality requirement. No such removal is claimed.

Lean045/046 pass with standard axioms, no source/runtime/artifact change.
Their full printed consumer statements and proof terms are in lean046/stdout.log.
Lean043/044 are superseded by carrier-preserving versions045/046.
This is a genuine weakening of the S2 record, not a proof of native S2CallerFacts.
