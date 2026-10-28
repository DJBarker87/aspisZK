# Budget and queue correction

The smaller initial cap of 50 Kani is binding despite the final job paragraph's
80. K041–K046 were compiler errors from the lane-owned `kani::old` annotation. K047, submitted at the stop boundary after the annotation repair, failed on missing Arbitrary for the borrowed Result return.
The local serial queue was stopped; K047 had already started before suspension,
completed, and was recovered normally. No host process was resubmitted.
A local attempt to reuse K047 was rejected by the wrapper before admission or
launch and consumes no second Kani run. `old(...)` is the documented syntax in
the pinned Kani installation. The queue now stops on compiler failures, in
addition to graph/lock/launcher failures. K048–K050 use the repaired inputs.
All failed runs remain in the receipt set; no verdict renaming or timeout rerun.

K024–K027 row getter scope is ONLY five-byte backing. The attempted broad-domain
reruns K041–K044 failed compilation, so they supply no broader native credit.
This domain mismatch is an OPEN caller obligation for nontrivial records.
K040 reproduces the borrowed-return stub generation limitation (missing
Arbitrary for &[u8]); it is not a desired failing fidelity control.
