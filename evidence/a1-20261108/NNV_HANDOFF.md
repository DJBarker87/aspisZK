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

Stage 3: common/afterstate source projections pass (L020/L037), as do the
same canonical semantic prefix calls (L036). Geometry callbacks (L013),
index ports (L021), abstract install projections (L023), selected projections
(L029), query branch normalization (L031), and selected prefix-products port
(L034) pass. No geometry/current/A1 closure is inferred from those inputs.
L030 failed at curried equality inference and kernel checking of the selected
prefix port; split into the generic source (L033) and explicitly typed selected
application (L034). Both replacements pass, no limits changed. L038's ambiguous
Prepared name is repaired with its full source namespace in L039.

Pins: NNV_RUN5B_OBJECT_PINS.json contains the read-only Run 5b object hashes;
NNV_TOOL_PINS.json pins Lean/lake and confirms the own launcher is an unchanged
copy of S2W_run_host.py. Each receipt pins selected direct objects and Aeneas
objects/sidecars resolved by its exact LEAN_PATH. No run-5b object is copied,
moved, deleted or rewritten. The own overlay is
`/home/dombarker/project-offloads/codex-cx-a1-20261108/NNV_objects`.

Setup note: the unchanged launcher was copied into the own workspace and
LEAN_PATH metadata uploaded before the first admission. All Lean source
uploads and scope submissions have allowed:true plus exit-0 admission, share
checks and disk receipts. No shared launcher/reservation script was edited.

Stage 4: replacement geometry source branches pass (L028/L031/L040/L041),
with named callbacks and independently checked installed scalar/std slots.
Prepared query carriers pass L039, including original Prepared roots, queries,
gamma and scratch. These are source transports on arbitrary pre-states;
no native/Kani bridge or ledger status is added by this Lean-only job.
