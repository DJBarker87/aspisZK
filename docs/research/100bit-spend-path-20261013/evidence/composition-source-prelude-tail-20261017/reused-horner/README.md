# Composition parts Horner proof reuse

This bundle preserves the exact green loop slice, loop adapter, symbolic Horner model, and the green caller-fold theorem with their individual build receipts. No Lean replay was started while assembling it.

The loop adapter proves actual generated loop success, canonicality, and decoded equality to the symbolic Horner recurrence for widths 24 and 4. The polynomial caller theorem derives the prepared multiplier, invokes both full loops, and identifies the result with the 29-entry lane sum. Its array/lane correspondence and caller-specific canonicality premises remain explicit.

`provenance/CompositionPartsLoopAdapter-04fc-provenance.json` compares the executable declaration bytes in raw candidate Funs SHA `04fc129bbd54c8792d5c11e6c017e810cfc68d7a4a9577eca9455088ed04a42e` to the older green slice input SHA `76abaf4cdd807726983f944b9e4710044f49e0a8a006ea1bdfd553fb00e3cc5c`. Each executable block hash is identical after stripping only the surrounding generated doc comment; no executable token was normalized. The older doc comments preserve different source line numbers.

Loop proof receipt: `receipts/loops/receipt.json`; caller theorem receipt: `receipts/polynomial/receipt.json`; Horner model receipt: `receipts/horner_model/receipt.json`. Exact source hashes appear in each receipt and in the file hashes below.
