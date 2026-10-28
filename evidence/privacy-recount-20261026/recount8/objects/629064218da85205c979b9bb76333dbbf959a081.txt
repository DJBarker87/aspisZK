# Native decoder boundary retained

The exact current `PV_RunJoin_Deployed.Runtime.disclosed` and `.observerOracle`
fields accept `Aeneas.Std.Result (Output N L C)`. The actual current
`RuntimeBody38.run` returns `PV_W_Threading.Run`, with world and ordered calls
retained for all three outer outcomes. The new source byte laws do not provide
a native observer implementation or a proof that a reachable failed/divergent
receipt can be decoded from the Result-only boundary.

No equality for either decoder has been supplied to CommonSample32 or
CommonObserver32. No fail/div branch has been replaced by successful output,
and no receipt has been erased to manufacture such an equality. The native
helper algebra and Memory associations remain explicit runtime data. This is
an outstanding proof obligation, not a shipped-source counterexample and not
a new trust item. Independent serialization prerequisites continue under the
standing instruction to retain an unresolved item and continue other work.
