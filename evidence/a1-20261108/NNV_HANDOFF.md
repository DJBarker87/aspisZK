# A1 NNV work in progress

Base 7f6c42c1ee5; 50 Lean scopes, no Kani or extraction. Target not yet established.
Read-only Run 5b objects, reference-only LEAN_PATH; own overlay NNV_objects.

Stage 2: Prepared input ports and full Result transport are split into
NNV_PreparedAtHost.source (L006), NNV_PreparedInputs (L007),
NNV_PreparedPorts.source (L011), and NNV_PreparedReturned.model (L015).
These prove the local same-input link, including returned errors and scratch.
They do not establish the earlier semantic caller or the later current body.
Semantic parse (L010), public transcript (L016), and begin (L017) pass.
All accepted printed axioms are standard only.

L014 concrete geometry polymorphic-slot rfl comparisons hit kernel memory;
that shape is retired, retained as NNV_GeometryStdSlots.lean.txt. Replacement:
abstract installer projections, then named instantiation, no cap change.
