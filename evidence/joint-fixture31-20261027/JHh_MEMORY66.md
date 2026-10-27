# Attempt066: isolated import and continuation replacement

Whole tree0C hit Lean -M7000, exit134, wall164.143210497s,
RSS7169636KiB,swap0, interpreter memory_exception. No theorem audit
line was emitted, and no closure credit is assigned.

Inspection found Port4B_Bounds was imported solely for two tiny batch-zero
wrapping arithmetic facts. It transitively imports CheckpointBytes5Output
via Port4B_Prepared. Replacement JHh_SmallConstants proves only those four
small scalar equalities (count0/slots0-2), without that import.

Tree0C is also split at declaration boundaries: levels06-08, levels09-11,
then levels12-17 and joins. This is a changed proof/import closure, never
a rerun of the memory-failed source. No cap or timeout is raised.
