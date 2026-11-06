# Failed steps (no credit)

NJF_K001: combined full-slice cut timed out at the existing 90-second harness limit (scope exit 1, wall 100.26 s, RSS 2789732 KiB, swap 0). No unchanged rerun or cap increase. Replacement keeps full child footprint but splits exact assertions into independent arbitrary-coordinate windows; scratch havoc uses raw per-field writes instead of an unnecessary 1024-byte copy inside the oracle. No custom copy stub is introduced; exact KMX remains applied to all reached copy builtins.

NJF_L001: unknown verifier.Error namespace. Added the actual AspisR1Stage2 namespace; no theorem from the failed module earns credit (its error-recovery sorryAx output is excluded).

NJF_K004 argument window timed out (wall 94.29 s, RSS 2727952 KiB, swap 0). Replacement isolates setup copies: initialize every Weights field directly in a preallocated MaybeUninit Box before constructing a valid Box<Weights>, avoiding whole-array copy lowering in arbitrary setup. All factors/points/extra remain arbitrary raw words, variant S2; no canonicality or guard restriction added. This changes the reduction shape, not the property. No unchanged rerun.
