# Strict47497 EXIT1 retained; constructor-summary discrepancy

The unchanged strict walker/collector ran ONE time on the90 NEW roots at
source8ffb2e3e9d70265c4a8a7512b980652738832958. Exit1,wall0:08.49,
peak6649708KiB,swap0. All walked axioms are standard;zero unresolved constants.
Original direct/augmented summary comparisons:89 agree,one disagrees at
PV_LIB_A_F6Constructors12.counter. Its direct #print axioms summary is[propext];
the raw graph also reaches Classical.choice and Quot.sound through the existing
PV_THR2_LibrarySemantics_AtomicUsizeNew.Returned.mk constructor type.

55350 is a focused DIAGNOSTIC ONLY, no declarations/new roots: Returned.mk
prints exactly[propext,Classical.choice,Quot.sound]; Returned and its value/world
projections print no axioms. Exit0,wall0:01.73,peak4623636KiB,swap0. Exact
receipt/source revision retained. The constructor occurs in counter's retained
REACHABLE.txt inventory. Offline union of each original summary with this
REACHED constructor summary agrees90/90. Exact per-root inventories/hashes
are in RAW_RECONCILIATION.json and RAW_GRAPH_ARCHIVE.json.xz.

This is NOT a second strict run and NOT a replacement EXIT0 audit. RAW_AUDIT
and receipt47497 retain strict_pass=false and original EXIT1. Walker,collector,
root arrays and proof sources were not changed after that walk. A future strict
comparison of these roots needs a CHANGED reached-constructor summary union;
never rerun the unchanged input. No source counterexample, nonstandard axiom
or full-joint contradiction follows from this diagnostic.
