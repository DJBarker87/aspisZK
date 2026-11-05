# Failed steps

L001 and L002/L004 were inspection attempts with incorrect qualified names; no proof credit. Their errors are retained in attempt stdout. L003 and L005 compile the actual new caller-entry theorems. No timeout or memory kill has occurred.

K002 is the expected matched control failure at the reachable forbidden digest, not a failure of the positive theorem. Verdict markers must be checked in final validation.

L019: own prelaunch pin check rejected missing NIC_PurityFrame.olean. The native setup script had overwritten NIF_PATHS.json with its older NIA-only seed list after the original setup selected NIC final/initial seeds. No compiler was launched. Restored the intended copied NIC-first path selection and removed the own script's path overwrite; no shared workspace or launcher changed. L020 is the first compile of FieldsEffect under the corrected input.
