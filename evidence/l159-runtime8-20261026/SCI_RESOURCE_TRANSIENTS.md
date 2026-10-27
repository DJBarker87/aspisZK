# Reservation transients

SCI_008's first reservation scan crashed with FileNotFoundError reading
/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice/run-rf6e90b552bc34361bbbe1506de470e5c.scope/cgroup.procs.
It was a vanished foreign scope. The unchanged task orchestrator followed
local-lean rule7: wait30s, retry once. Admission then succeeded. This launched
no extra Lean attempt, and no launcher or reservation infrastructure changed.
The final barrier receipt and retries JSON are retained.

SCI_011's first scan similarly hit vanished foreign scope
run-redf27e7d35ec42fab1cc956bdf90f3aa.scope/cgroup.procs.
Its rule7 retry returned ordinary reservation contention (48GiB already
reserved, plus requested8GiB >55GiB). The orchestrator waits180s and retries,
at most10 times. No barrier bypass or cap increase.
