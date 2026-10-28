# Search-prefix check correction

The initial preflight (before attempt 42600) checked all 5,673 external object
bytes under the inherited runjoin prefix, matching h4/SCOPE's manifest. The
private runner used env-J's base prefix plus this job's new object directory.
The difference in search roots was noticed after attempt 42612; no host scope
was then running. actual-prefix-preflight.py checked the exact private J.json
and found all 5,673 selected objects byte-identical to the same manifest, with
zero mismatches. Thus no different external object bytes were loaded; however,
the path-selection check was late. This chronology is retained explicitly.
Subsequent checks use the actual private environment. No unchanged full replay
was run to conceal the correction. The final focused audit will record it.

Attempt 42619 exposed a dangling symlink at the first Aeneas root in base J.
Python is_file() had skipped it, whereas Lean selected it and failed before
loading Aeneas. The second check therefore also did not model Lean lookup
faithfully. No theorem from 42619 was accepted. prepare-external.py now verifies
and links the exact 5,673 manifest objects (plus recorded available companions)
in this job's first private prefix. This avoids every dangling shared alias,
without repairing or overwriting any shared object. The strict check selects
existing OR symlink entries, has no manifest fallback, and passed for all
5,673 objects before the next compile. The environment change is the recorded
reason to retry the failed inspection. The mathematical modules compiled
before this correction did not import Aeneas; their axioms/results are retained
as focused evidence, with this preflight chronology rather than a release claim.
