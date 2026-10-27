# Job input correction before attempt 009

Eight modules compiled successfully. The dependency pin step for RPt_BEi_CutProjection
then found that this job’s configured LEAN_PATH omitted RPz8_overlay.
No compiler ran for that ninth invocation; no failed source was retried.
A first string replacement did not change the path, so the pin-only check
failed a second time before compilation. Both tracebacks are retained.
The verified job path now includes RPz8_overlay after RPt_overlay and before RPz7_overlay,
exactly retaining the RPz8 predecessor order. No host launcher, monitor,
admission script, library, or inherited object was repaired or changed.
The original console traceback remains in RPt_build-console.log.
