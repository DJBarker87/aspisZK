K027–K044 are excluded target-selection failures. The strict KMX auxiliary-file
validation added before K027 reused the identifier h, overwriting the requested
harness with the final expected hash. Cargo Kani therefore selected NO harness.
All18 invocations remain charged. Their configured intended target is in each
receipt; their ACTUAL --harness argv (the hash) is printed in stdout.log.

Fix: name that validation variable expected_hash and assert the actual argv's
--harness argument equals the requested sys.argv[2]. The validation remains at
least as strict. Queue now halts on a missing-harness diagnostic. No native or
Lean theorem credit is inferred from these failures. The previous serial queue
continued independent targets because it classified every positive non-pass as
an independent failure; that was inappropriate for an own-runner target error.
No lead launcher, shared workspace or reservation tool changed.
