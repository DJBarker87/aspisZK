# Continuation selection notes

RPu_plan.json pins the selected source and import mapping for every new context.
RPu_inherited-pins.json pins the immediate RPt handoff/frontier/plan and pin sets.
RPu_inherited-object-pins.json records the 2500 retained paths rechecked remotely;
RPu_inherited-host-check.json reports no mismatches. This is a direct pin check,
not fresh compiler credit for unchanged libraries or repository contexts.
The RPt/RPz8/RPz7/trusted views remain in the same order, with RPu_overlay first
among repository views, after the pinned Lean 4.32.0 library. All new names are
unique RPu names, so no predecessor object is shadowed or overwritten.

23 historical resolution decisions and Aeneas toolchain classification are
inherited through RPt_inherited-pins.json to the RPz8 evidence. RPz3 failures were
addressed by successors; this job does not retry old failed sources or substitute
alternate files. The new prepared-channel-loop source selection is checked
against the coherent host source in RPu_STATUS.md. Aeneas.Std.WP is unchanged
pinned trusted library b31feadf785e24f1666d5a16c30f8846969e0901df09cc8d2678c9212622def4.
