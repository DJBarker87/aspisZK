# ELF rebuild blocked by host linker task creation

LPa_SBF_default: exit1, wall27.5070190349943s, peak430352KiB, swap0.
The exact admitted command, source snapshots, cgroup peak and limits are in
LPa_SBF_default/receipt.json; the complete compiler/linker output is stdout.log.

The native host linker for serde_json's build script aborted:
`terminate called after throwing an instance of std::system_error`
`what(): Resource temporarily unavailable`
`collect2: fatal error: ld terminated with signal 6 [Aborted], core dumped`
`error: could not compile serde_json (build script)`.

This is not a memory kill, failed Lean theorem or ELF hash mismatch. No ELF was
produced for comparison. No cap was raised and the failed command is not rerun.
Per local-lean rule5, no host/launcher/linker infrastructure repair is attempted;
the SBF chain stops here for the lead. Devnet and Pool are NOT launched or
claimed rebuilt. The required three-ELF pin gate remains OPEN. Independent
focused Lean proofs continue on the already-working capped Lean launcher.

The source reversal audit proves all original production source bytes are
retained after removing cfg(kani)-only additions, and original line numbers
are preserved. This does NOT replace the required ELF rebuild gate. Inherited
pins remain historical evidence only. No new release result is claimed.
