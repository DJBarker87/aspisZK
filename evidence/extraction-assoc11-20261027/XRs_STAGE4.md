# A3 base-field transport and final axioms audit

L093-L097 privately restore unchanged LPe/LPf and LPh_FieldValues prerequisites.
XRs_BaseMultiply (L099) identifies XRn's actual reducer and base multiplication
with FIo_Native, then reuses LPf_BaseMultiply.source for totality, residue value
and canonical output on arbitrary U32 inputs. It reuses LPh.m31_mul_value to
identify the complete Result with emitted semantic-call base multiplication.
This is not yet CM31/QM31, mul_u or the installed powers29/claim transport.

L098's broad definitional conversion reached the DEFAULT heartbeat limit;
its module and sorryAx diagnostics receive no credit. L099 replaced the
conversion with explicit symbolic unfolding of the two reducer definitions
and their P constants, then a named same_reducer rewrite at multiplication.
No timeout, cap, heartbeat or recursion limit was raised; no unchanged rerun.

L100 imports every successful new proof module (12), XRq_Audit and LPk_Result.
All 28 new theorem audits plus both reused leaf/non-vacuity audits pass with
only standard axioms or none. Exit0,1.640461084s,4744388KiB,swap0,revision
ba38edd4bb9332212079641ace1b65ffe62dc3e3; exact source/object/tool hashes and
command are in the receipt. The adopted root was separately audited at L084.

Budget EXHAUSTED:100/100 attempt identifiers,99 actual Lean processes plus
L027 pre-compiler missing-import failure. No more prover work is authorized.
Kani0/10; no native body or harness changed, so no new native gate applies.
A2 and A3 OPEN; all A0-A8 OPEN. Actual top premise removal ZERO.
