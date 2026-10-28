# NBJ scheduling exception

Journal recovered read-only on 2026-10-28: K001 scope started 00:50:49 UTC,
terminated 00:51:12; rejected L001 started 00:51:02, terminated 00:51:07.
Five seconds overlap violated the one-scope-per-job rule. Both scopes retained
6G/8G/swap0/64 limits and allowed admission receipts. This is a policy failure,
not an infrastructure failure; neither cap nor reservation was bypassed.
K001 is a passing native check; L001 is rejected, including recovery sorryAx.
Subsequent submissions wait for terminal receipt recovery before launching.
No claim that all NBJ attempts were serial is permitted.

Own NBJ_host.py was strengthened after K027: before admission/submission it
checks the host process inventory for an active NBJ S2W runner and refuses
the launch if found. This repairs only the job's own wrapper; it does not
modify any shared launcher, admission or monitor. The check strengthens the
previous validation. No mutex/flock wrapper is introduced.
