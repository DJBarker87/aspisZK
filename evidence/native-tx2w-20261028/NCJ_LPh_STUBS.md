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
