# Actual decoder agrees with the typed coefficient payload

The successful actual 28-coefficient decoder now produces the same coefficients as the retained typed coefficient decoder on the same original record payload. The proof derives all 28 field-value equalities through actual parser traces and the previously proved strict-chunk bridge. No independent field-value correspondence is assumed. It reuses the existing typed decoder characterization and strict low-chunk codec.

The remaining premises are actual decoder success, the 896-byte payload length, and strict low-chunk validity for each original payload slice. Connecting those premises to the same accepted caller/view, and connecting the resulting row to the semantic polynomial, remain separate obligations.

Lean 4.32 exited 0 in 7.11 seconds, peak RSS 3,228,434,432 bytes, zero process swaps; the printed theorem uses only propext, Classical.choice and Quot.sound. This is focused working evidence, not a unified release replay or the complete 100-bit soundness theorem.
