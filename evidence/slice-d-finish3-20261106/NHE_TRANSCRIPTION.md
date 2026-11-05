# Polynomial transcription under ruling (ah)

The failed NGM_E003 extraction is retained by hash in NHE_INPUT_INDEX.json. NGW_E001 extracted the loop-free eight-limb add reference; its existing NGW_PolynomialAdd.observed and NGW_Horner.cell laws are reused, with no extraction rerun. The frozen source snapshot is NHE_frozen_polynomial.rs.txt, checked against revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 by NHE_polynomial_validate.py.

| Frozen source / safe reference | Lean correspondence |
| --- | --- |
| `(0..7).rev()` | NHE_Polynomial.indices = 6,5,4,3,2,1,0; retained NGM_K100 / NGW_K034 pass/fail pair observes exact native order/count |
| `.fold(E::ZERO, ...)` | NHE_Polynomial.zero and NHE_HornerPort.go; zero multiply is retained, not simplified away |
| receiver `a.mul(x)` | first bind in go; NHE_WidePort.adopted identifies the emitted product with FIn_Polynomial.mul on SAME canonical a,x |
| argument `field(bytes,i)` | second bind in go; NHE_FieldPort.adopted transports the SAME bytes and index to FIn_Primitives.field, including all failures and divergence |
| `.add(coefficient)` | third bind; NGW_PolynomialAdd.observed identifies the extracted reference's eight outputs; NGW_CurrentAddPort.adopted identifies the SAME native add with FIn_Primitives.add |
| next fold accumulator | recursive argument next; canonical product from LPi_TowerValues.wide_mul, coefficient from NHE_FieldCanonical.success, next from NGW_PolynomialAdd.total; NHE_HornerPort.adopted proves induction |
| returned accumulator | NHE_Polynomial.cohort transports the complete Result into FIn_Polynomial.polynomial; no accepted polynomial or successful parse supplied as an input |

The native one-cell observation packets are the five retained NGM_K088..097 pairs: both four-word output halves, exact multiplication operands, SAME coefficient window/index/value, source call order/count. The reverse-fold pair is retained rather than re-run. NHE_POLYNOMIAL_VALIDATION.json validates every original graph-before/immutable-lock-after/offline configuration and intended failing assertion. KMX patch hash is recorded there; no custom copy stub.

Domain: canonical evaluation point; arbitrary immutable byte slice. Native parser rejection/divergence is preserved. Every index is <7, hence below the field port's proven <64 domain. No caller canonicality obligation is stronger than NGM_DOMAIN.md's canonical alpha; short/malformed slices are also covered by this complete-Result association.

This is reviewed hand transcription of the fold under (ah), with emitted parser/arithmetic carrier laws and extracted add reference. It reclassifies native semantic transport within P6/D188 option A; it removes no trust item and does not prove the headline. No successful child premise, allocation-success premise, fresh native result or opaque whole-fold multiplication harness is used.
