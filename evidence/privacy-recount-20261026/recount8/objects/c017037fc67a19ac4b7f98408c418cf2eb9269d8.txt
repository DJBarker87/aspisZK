# h7 source-cohort findings

R1PublicCodecAgreement resolves through the EJR row named PublicCodecAgreement,
whose resolution path is R1PublicCodecAgreement.lean and whose blob and sha256
match the accepted variant. This is h5' precedence over the other tracked copies;
the failed-codec and recovered variant are not selected.

WithdrawalValidation.Funs resolves through h7(2). EJS resolves its importer
WithdrawalValidationAmount431 to source sha b9391593… . The withdrawal manifest
pins that same importer and Funs sha 9f63864a… together. Attempt-c artifact-pins
also pins that exact generated Funs file. Every link and file hash was checked.
This establishes source identity, not deployed feature/body fidelity or a theorem.

SelectedMaskProbe.Funs and .Types are named by host-module-graph.json. Neither the
graph's resolved path nor raw-object-pins' selected import-union object path exists
on the host. No object was loaded. In addition, their recorded transitive cohort
contains 19 external object hashes different from the mandatory current h4
manifest (including Aeneas.Extract.Extract and AeneasMeta.Extensions). Even a
restored object with the old object hash would not by itself pass h6 dependency
checks. The exact 3839/3837-entry closure checks and all variants/hashes are in
h7-resolution.json; the external mismatches are extracted separately.

No importer-generation receipt hash chain selecting a tracked alternative for
either SelectedMaskProbe module has been established. They are reported cohort
gaps under h7(3), not Lean counterexamples. No oracle cone was staged or imported.
Only that dependent step stops; independent current-emission source laws continue.
