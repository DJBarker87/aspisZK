# Contract domains and substitution gates

A `stub_verified` spelling is never counted as proof of its callee. Only an
accepted callee receipt for the identical body/specification permits a caller
claim. Unrun/draft harnesses in a scratch patch supply no closure.

| Native function | Exact domain | Postcondition / present status |
|---|---|---|
| core field reduce_u64 | Every u64; no precondition | Two natural31-bit folds, one subtract, result<P. K004 PASS. |
| canonical::reduce | Every u64; no precondition | Same exact value law. K011 PASS. |
| M31::mul, exact | All raw u32 operands; no precondition | product's exact two-fold residue and <P. K006 stubbed/K007 inline TIMEOUT; not available for substitution. Lean source total/exact theorem is distinct. |
| Q::raw | All four limbs of each operand <P | Four exact raw representatives; K012 TIMEOUT; coordinate2 K013 TIMEOUT. No caller substitution. Private representation invariant/caller installation still requires association, not an assertion that the whole caller was checked. |
| Q::mul | Same canonical operand precondition | All four reduced raw coordinates and <P. Draft contract, not checked or installed. |
| CM31::write_le_bytes | Output slice length exactly8; input limbs unrestricted u32 | Eight exact bytes plus modifies footprint. K015 dynamic footprint PASS, but K016 parent has compiler ICE. K017 eight single-byte footprints FAILED bulk-memcpy assigns check; excluded. K018 one sized8-byte-array footprint PASS. |
| QM31::write_le_bytes | Output slice length exactly16; input limbs unrestricted u32 | Sixteen exact bytes. K014 dynamic footprint TIMEOUT. K019 with two verified CM31 calls and sized footprints TIMEOUT; no available parent contract. |
| WideExact::to_le_bytes | Valid native E (canonical limbs by private type); no additional requires attribute |32 exact bytes. K020 TIMEOUT. Full E domain was generated with from_limbs, no sparse/diagonal restriction. |

The checkpoint's put_k and both semantic/Z serializer loops construct `[0;16]`
before every QM31 writer call; the exact length16 precondition is therefore the
source-established size. A QM31 writer's `[0..8]` and `[8..16]` subslices have
length8 whenever reached. No input canonicality precondition is imposed by either
raw writer. Native caller proof receipts must still verify these precondition
checks on their same execution; no timed-out caller is credited with that result.

The next byte-writer proof change shares each reference byte array once in the
postcondition. This preserves every precondition, byte assertion and footprint;
it does not weaken the target or increase resource/timeout limits.

A future bound-only M31::mul contract/powers canonicality probe, if run, must be
labelled only as safety/canonicality. It cannot replace the exact multiplication,
powers value law, semantic fold or prepared_claim join.

## Allocation-context qualification

K015/K018/K022's concrete harness output is an owned `[u8;8]` array. Those
receipts are **not** silently promoted to every possible backing allocation for
an eight-byte slice. K026's caller-crate registration of the same root8 harness
times out. The native QM31 caller passes offsets0 and8 of an owned16-byte buffer;
K028 therefore checks those actual subslice contexts and the untouched half.
No whole caller receipt is credited before that contextual obligation is settled.
The annotations' length precondition alone does not erase this proof-domain gap.

K024 fails before verification because cross-crate verified substitution needs a
caller-crate proof_for_contract registration. K025 also fails before verification:
an unused powers draft had a missing M31 registration. It was removed; neither
failure is a pass, and no unproved powers stub was executed in a credited target.
K027's checksum source cut reaches no substituted byte writer: its proof is
independent of the still-open byte-writer caller context.

## Final native status

K028's variable half and K029/K030's fixed offsets0/8 all TIMEOUT. Contextual
CM31 substitution remains OPEN; the64-weight and whole-checkpoint caller drafts
are UNRUN. K031's raw coordinate3 contract also TIMEOUT.
K032 independently checks M31::mul's weaker `result.0<P` postcondition with no
precondition on either raw u32. This DOES NOT replace the exact product equation;
that target remains OPEN with its original failed receipts. The final scratch
M31 annotation is this explicitly bound-only diagnostic contract. Its intended
powers caller is a canonicality/safety probe only, but G033's infrastructure
failure prevents even that K033 run. No exact powers value result is inferred.
