The actual full-SDK `require_readonly_account` cut is blocked in Aeneas type
analysis. Charon succeeded; Aeneas rejected the `NonNull` pointer-pattern type
inside the real `AccountInfo` carrier before translating the function. No Lean
file, axiom audit, or actual guard theorem resulted.

Run `python3 verify.py` here for read/hash-only verification. Run
`python3 ../../tools/readonly-account-extraction-kit/extract.py --check` to
independently check the unchanged source span and imports. Neither runs a
compiler. The complete report is
`../../design/J1-READONLY-ACCOUNT-EXTRACTION-20261016.txt`.

The archive retains the exact kit/locks, all 67 dependency or reexport-provider
crate archives, 1,873 individual source-file hash comparisons, LLBC and full
opaque/foreign/Error inventory, raw Charon/Aeneas output, enforced resource
receipts, tool/runtime pins, actual SDK/Rust source snapshots, and the separate
read-only audit/preflight failures. The source file pin for Aeneas's failure
site references the already retained matching native-tools source archive.
The selected lock contains 91 registry entries; 65 participate in the Linux
metadata graph checked for this attempt. No cache or generated type was
modified to bypass the failure.

The resource reservation is released. Repeating this unchanged attempt or
substituting an abstract account carrier is not part of this checkpoint.
