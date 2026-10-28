# Own runner/proof repairs

The NBD serial controllers were copied under NBH and adjusted to this job workspace, source lists and evidence directory; S2W/S2H infrastructure stays byte-identical. Metadata parses only the JSON line, diagnostics separate. Validation remains frozen graph equality + offline + before/after frozen lock hashes.

L001 rejected unsupported `step* only` syntax. L002/L003 rejected the explicit Fin witness bound; changed to Nat.le_refl. L004/L005 pass. L006 rejected ambiguous constructor elaboration in a manually duplicated monadic expression; L007 instead targets the actual definition directly. Rejected sorryAx output is diagnostic only, never accepted evidence. No timeout/memory kill or cap increase.
