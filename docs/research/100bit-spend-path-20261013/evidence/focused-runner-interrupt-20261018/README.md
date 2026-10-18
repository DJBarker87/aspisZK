# Focused job interruption and resource-stop evidence

A two-job focused Mac trial stayed below the8GiB aggregate Lean RSS guard but increased system swap use. The extra callback job was stopped and serial formal checking restored; its logs/source are diagnostic only, with no accepted theorem/object claimed. Parent interruption exposed an orphan-child cleanup bug. Root identified and terminated only that job's process group; the other proof job was untouched.

The revised runner catches controller interruption/error, terminates its own child group, waits, then retains the terminal receipt. A tiny no-import sleep fixture sent SIGINT to the controller and verified child exit-15 and no surviving fixture Lean process. This fixture is a lifecycle check, not a formal proof; time-wrapper metrics may be absent after group termination. Old/new runner sources and the cleanup result are retained.

The callback source was not rerun with a larger cap. Future formal targets use one serial Mac lane; the NUC lane retains unchanged per-job caps and its separately reviewed reservation/watch gates. No production Rust or security theorem changes are made by this operating-tool fix.
