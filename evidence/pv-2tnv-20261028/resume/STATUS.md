# D408 resume in progress

Entry HEAD d13b5f585b4918648d13cd9bfd098a1d0507f9d5 on codex/pv-2tnv-20261028.
60 normal attempts, 0 Kani, at most one lead-run AGG16; no AGG16 requested.
Runjoin source is inspected read-only; no runjoin module is edited or duplicated.

The native fixture is transfer-13 (snapshot index 13, after index 14), unlike
runjoin's index-zero canonical fixture. A byte-level same-payment fact is being
checked: TX2 request.drop 104 = TX1 public bytes.drop 1664. The 216-byte equality
is preflight-checked, not yet a kernel theorem. Canonical witness construction
still needs the transfer-13 AppendBinding and source-to-headline projection.
FixturePdaRuntime remains NOT discharged; no privacy adoption or T change.

60900 launched and failed at import: shared env/J first LEAN_PATH prefix contains
a dangling Aeneas.olean link. RSS 189572 KiB, swap 0, wall 1.077782 s, exit 1.
No theorem credit. The next input selects the existing read-only Stream B
runjoin16 std-cache prefix (no host files repaired), after rechecking its
external object hashes against h4. This changes the environment and dependency
fingerprint; it is not an unchanged rerun.
