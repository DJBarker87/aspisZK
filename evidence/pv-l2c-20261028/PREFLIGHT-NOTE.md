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
