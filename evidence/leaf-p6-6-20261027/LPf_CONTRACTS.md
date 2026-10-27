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
