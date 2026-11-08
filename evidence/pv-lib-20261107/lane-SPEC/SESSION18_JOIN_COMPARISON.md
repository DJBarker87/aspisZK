# Before/after — thread-29′ lane A interface

BEFORE: LaneAJoins16.history stack n = run (cut stack) parameters n
(initial Entry14.input). Original85 returns the fixed Tls85Data16.at85.
Joins, OriginalToF6, F6ToRange, RangeToF361 and F361ToInit all use that history.
The complete old module remains byte-identical.

AFTER: LaneAJoins18.history entry activation n = History18.history entry
activation n = run (cut (EntryWorld18.frame entry activation)) parameters n
(initial (EntryWorld18.input entry.world)). Entry includes the complete entry
Pre, paired run coordinate and finite nonwrapping stack grant. Original85
returns World18_Tls85Data16.at85 entry, and is proved for every entry/activation.

All milestone predicates, source body drops92/113/129, index orderings,
activation equalities and InitPoll requirements are unchanged. Only the entry
world/derived native frame are parametric. There is no BODY success, native
answer, physical-register map, Store delta or ownership conclusion in Joins.
The frame activation remains finite data; its relation to the reached source
frame must still be derived at native use. No join is claimed inhabited here.

The concrete instance uses parent1024, scope entry1016, run1136 and grant
[512,1536). This is one original start; no suffix restarts at an internal entry.
