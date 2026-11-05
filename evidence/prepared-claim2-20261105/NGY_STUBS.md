# Oracle/stub inventory

No field multiplication is executed or proved by Kani. No new field stub.

| Native substitution | Paired Lean law | Domain / effect |
|---|---|---|
| EbyKDot::push -> local oracle, source cut | NGU_LPm_PublicPort.source; NGU_LPm_PointLoop.model_push; NGY_Oracle.child (pending compile) | Native caller initially permits arbitrary full Result and full Dot poststate. Installation requires canonical eight-word value/four-word scalar, count<29, and the SAME logged prestate. Only c0.sums/c1.sums/count may mutate. |
| copy_nonoverlapping / [u8]::copy_from_slice -> KMX originals | KMX_CopyMeaning existing value laws, NGU original fidelity controls | Exact original patch and hash validated before each run; new caller corruption control required. |

KMX patch reference: evidence/kani-mitig-20261028/KMX_copy_stubs.patch; NGU_KMX.patch is the inherited byte-identical transport input. Its three source hashes are enforced by NGY_gate.py. All logs are local owned records. No static writes or Option<fn> properties. There is no stub_verified use yet. No contract semantic transport credit is claimed until its appropriate shape controls and matched corruption control pass.
