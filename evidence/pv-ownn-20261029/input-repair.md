66400 failed before elaboration because the task preflight copied the ownc
ownership cache but did not materialize ProverRwFullTypes in the private prefix
required by run2.py. The dependency planner incorrectly marked both full-type
objects ready from the environment. They are now included as pinned prerequisite
targets 66401/66402; 66403 rechecks unchanged PV_OWNM_V239 only against those
changed dependency inputs. No unchanged failed source+dependencies resubmission.
No shared runner or cap changed; failure is charged and receives no credit.
