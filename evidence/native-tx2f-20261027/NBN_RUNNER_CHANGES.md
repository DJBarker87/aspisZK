# Own-controller changes

NBN_build.py/NBN_native.py derive from the inherited NBK own controllers with prefix/workspace/budget substitutions. Shared S2W backends, reservation scripts, shims and coherent objects are untouched. Native output printing was reduced to the final900 characters; full stdout and receipts are retained.

NBN_CONTROL_SYNC's initial upload failed with `/bin/bash: Argument list too long` before any write or prover launch. Repaired our own sync script to compare the frozen parent SHA-256 then append only its cfg inclusion, rather than passing two copies of the frozen source in one SSH argv. This is equally strict validation. The next metadata preflight NBN_G002 detected the missing own harness and launched no process; NBN_K002 has no solver/receipt and is conservatively counted as one attempted native slot. No unchanged submitted process was resubmitted. The distinct K003 source/setup passes complete frozen graph equality and unchanged lock checks.

NBN_L045 admission is waiting on the unchanged reservation barrier (allowed:false); no refusal is treated as a launch. Every retry log is retained. No cap increase or second simultaneous scope.
