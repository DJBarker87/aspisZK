# Historical ELF source gate does not cover the merged tree

The required merge completed without conflicts at
f18cb491c92bc8a08955af0ce119d561f7857b35. It changed nine crate files relative
to the runjoin entry revision. The inherited batch2f ELF gate records three
matching release pins at 763e429f184b932ca5c52633b7fa2a98a3b36b6f.

An explicit `git diff --quiet 763e429f184b932ca5c52633b7fa2a98a3b36b6f HEAD
-- crates programs` exits **1**, with 21 differing paths. Full path lists and
the nine merge-changed source hashes are in merge-source-identity.json.
Therefore that historical gate does not validate the current merged tree.
No three-ELF rebuild or deployed-client feature/body association was run here.
Frozen-source/deployment credit is withheld; the gate requires new checks or
an independently verified applicable source/artifact association.

The earlier PLAN/commentary identity assertion was erroneous: a compound shell
command continued to subsequent reads, and their successful exit was mistaken
for the diff's exit. The claim is explicitly withdrawn in PLAN and commentary.
This was found at final evidence collection after the 100-attempt Lean budget
had been exhausted. The source theorem audits do not establish artifact identity.
This is not a checked counterexample to privacy or to any ROWS statement.
