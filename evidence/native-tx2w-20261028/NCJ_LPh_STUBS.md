# NCJ opaque-call log substitutions

No field multiplication is evaluated in Kani. Opaque replies are arbitrary
canonical values; Kani establishes routing and linear combinations. Native
log-to-emitted-call association remains part of the named enclosing bridge.
A local gate is not a full source refinement.

| Scratch replacement | Emitted-ok value theorem | Domain / caller obligation |
|---|---|---|
| `NCJ_qmul` / `QM31::mul` | `AspisR1.LPi_TowerValues.qm_mul`; `NCJ_CallLog.qm_reply` | Both QM31 operands' four limbs < 2147483647; input generators, U01 sub/add canonicality, then same logged replies. |
| `NCJ_emul` / `WideExact::mul` | `AspisR1.LPi_TowerValues.wide_mul`; `NCJ_CallLog.wide_reply` | Both eight-limb operands canonical. Inputs and prior emitted-ok replies establish this. |
| `NCJ_eqmul` / `WideExact::mul_qm31` | `NBG_FieldDischarge.wide_qm` | Wide operand canonical; QM31 operand is normalized by this emitted definition. Native producer still proves its public canonicality. |
| `NCJ_emmul` / `WideExact::mul_m31` | `NBG_FieldDischarge.wide_scale` | Total emitted law; scalar normalized modulo P. |
| `NCJ_quarter_mul` / `M31::mul` | `NCJ_CallLog.quarter_square` | EXACT arguments 536870912,536870912, asserted in the stub. Reply 134217728. No broader base-product replacement. |

Identical `x.mul(x)` calls in frozen `double` have independent arbitrary
replies in Kani. `NCJ_CallLog.repeated_qm` and
`NCJ_DoubleAssociation.sharing` identify their replies only after substitution
by the deterministic emitted definition. The constructor model shares one
product; its source is not silently described as byte-identical to frozen Rust.

Only green Lean receipts authorize the above new theorem names. Failed attempts
are retained and earn no theorem credit. Canonical-domain composition and the
full source-to-cohort association are tracked per function in the U12/U13 ledgers.

KMX: the exact `evidence/kani-mitig-20261028/KMX_copy_stubs.patch` is installed
in the scratch root; `NCJ_KMX_SHA256.txt` pins its SHA256. No custom copy stub
was written. K002 is the matching pointer negative control (FAIL); K003 is
positive (PASS). Every reached copy family needs its corresponding matched
control before credit; additional families are not inferred from pointer credit.

U13 additions: NCJ_scale is the same WideExact::mul_m31 replacement paired with NBG_FieldDischarge.wide_scale; NCJ_mul is paired with LPi_TowerValues.wide_mul. NCJ_field is an OPEN decoder callee overapproximation, with exact byte/index logs and canonical outputs; its model value/Result is NBQ_FieldTotal.range plus NBG_WideBytes.bytes_result, while the general native slice association remains an exact lower obligation. NCJ_poly is an OPEN whole-polynomial substitution. No pass of the enclosing control gate discharges that callee bridge.

Dot fragments: NCJ_raw / canonical::Q::raw is paired with AspisR1.LPi_RawValues.source on both private Q operands' canonical four limbs. The native stub ASSERTS those domains on every call, returns arbitrary four U64 words, and logs both exact operands. The actual public checked_q/from_wide and count checks run. Natural raw substitution and public/count invariants are inherited from NBQ_U06 and NBQ_PublicInvariant, with the inherited native/copy qualifications retained.

Final native additions: NCJ_kind / process_kind is an OPEN call-logging callee
replacement in K063/064; the positive timed out, so no enclosing native credit.
NCJ_field remains OPEN as an all-context callee. K065/066 and K067/068 instead
execute the actual frozen decoder on one arbitrary canonical32-byte window
within arbitrary224/2048 bytes, with arbitrary limb selection. These are
successful local native facts and do not silently discharge typed all-context
Result/carrier association. K069 and K070 are the matching exact-KMX to_vec
and slice negative controls, both FAIL. No whole-polynomial stub is CLOSED.
