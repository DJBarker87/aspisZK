# D577 alias-safe final client — gates in progress

The preliminary report is superseded by the checked native stdout-alias counterexample N91105 (alias-counterexample.json). The previous29f011ca binary is NOT the final client. Its N91104 differential was deliberately stopped,authoritative exit143,and is not credited as a final PASS. Existing private corpus and keys are retained.

Source repair `0e3df6e684` compares device/inode identity of the output FIFO against stdin,stdout,stderr and the input FD before any witness read. Re-extraction N91106 is running; the final optimized client SHA and the alias controls plus a new100-pair differential remain pending. The existing NEP audit is reusable only if the actual regenerated computational Types/Funs and external signatures are unchanged; the extraction script checks this explicitly. No timing run or privacy endpoint claim.

See REPORT-before-alias.md for completed preceding proof work and the failures that remain preserved. This report will be completed from the corrected final gates.
