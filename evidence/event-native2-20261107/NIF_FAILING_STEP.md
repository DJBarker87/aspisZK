# Failed steps

L001 and L002/L004 were inspection attempts with incorrect qualified names; no proof credit. Their errors are retained in attempt stdout. L003 and L005 compile the actual new caller-entry theorems. No timeout or memory kill has occurred.

K002 is the expected matched control failure at the reachable forbidden digest, not a failure of the positive theorem. Verdict markers must be checked in final validation.

L019: own prelaunch pin check rejected missing NIC_PurityFrame.olean. The native setup script had overwritten NIF_PATHS.json with its older NIA-only seed list after the original setup selected NIC final/initial seeds. No compiler was launched. Restored the intended copied NIC-first path selection and removed the own script's path overwrite; no shared workspace or launcher changed. L020 is the first compile of FieldsEffect under the corrected input.

L025: own audit input list requested an unused NIF_Driver.lean, while this job has only the actual NIF_ProofDriver binary. No process was submitted. Removed that unused source from the own runner's audit inputs; the actual ProofDriver source, roots, expected imports, walker pins and audit command are unchanged. L026 performs the first fixture replay.

L008-L010: fixed 32 byte-list/getD proof drafts failed (including a misnamed list lemma and missing numeral normalizations); replaced by the retained endian bridge and exact getD identity, passing L011. L012-L013: read_total drafts failed on wrapping-offset bounds and one extra tactic after a closed goal; passing replacement L014. L017: wrong namespace for the actual closure trait; corrected to Port3_NativeQueryBody and passes L018. Failed draft objects are excluded from the final scan/export/audit, not admitted via recovery sorryAx.

Final failed stage: the larger native NFS effect association is NOT established. Missing callee/native source-stage laws, not a proved mismatch or tool resource limit: private EbyKDot push/finish and exact caller/state associations, accumulation Vec/push/frame orchestration, and SAME-parent installation of the local fold/other event windows. The 80-slot native allocation is exhausted. NHZ_DRIVER cannot be re-instantiated with a nonexistent physical packet; no desired-success premise is added. All remaining independent model arms are already proved/reused, as itemized in NIF_REMAINING.md.
