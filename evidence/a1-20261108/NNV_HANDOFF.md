# A1 NNV final handoff

Final validation: **50/50 scopes**, 37 passes and 13 failures (includes
inspection/import scopes; these counts are not security progress). Kani 0,
extraction 0. NNV_COMBINED_IMPORT passed L050: exit 0, wall 31.183832312 s,
peak RSS 6,951,312 KiB, swaps 0, source revision 51fbb8b4279 (dirty evidence
snapshot hashes retained in the receipt). It imports NNH_Run5bCombined and
all 34 accepted NNV proof modules. Every printed root has only standard
axioms. NNV_COMPILE.tsv and per-attempt receipts record exact targets,
commands, source/dependency hashes, exit, wall, RSS, swap and axioms.

No term of the requested `RSL.TAS.NND_A1` type is delivered. No ledger row is
closed. This is local source correspondence support only. The 100-bit,
privacy and two-transaction release targets and trust boundary are unchanged.

The exact OPEN field is:
```lean
RSL.TAS.NND_A1 (AspisR1.NNH_Run5bHost.S_host L0 copy std)
  NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C
```
There is therefore no delivered-constant `example : <type> = ... := rfl`, and
no raw ax2 audit of an A1 term. `NNV_REMAINING.md` lists every open member.

Reusable roots include `AspisR1.NNV_PreparedNative.returned` (P reply and
scratch at canonical ports), `AspisR1.NNV_CurrentGeometry.source/returned`
(full outer source loop and current geometry at canonical raw indices),
`AspisR1.NNV_SemanticPrefix.returned` (through begin, finish still open),
`AspisR1.NNV_CommonAssociation.common/afterstate`,
`AspisR1.NNV_AfterstatePort.source`, `AspisR1.NNV_CheckpointDigest.source`,
`AspisR1.NNV_CheckpointValue.source`, and `AspisR1.NNV_DecodeP1880.returned`.
Their exact types are in the correspondingly named committed Lean modules;
NNV_ACCEPTED_ROOTS.json contains each printed axiom line.

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

Stage 5: NNV_GeometryBody.source (L042), NNV_GeometryOuter.loop/source/stage
(L043), and NNV_CurrentGeometry.slot/source/returned (L045) pass. The generic
outer source loop is transported by equality of its arbitrary-state bodies,
using the previously checked reverse-product loop; no concrete loop or buffer
is normalized. The current port is at canonical natural-to-raw indices and the
SAME Prepared queries, including full Result association and returned Ok.
L044's unsupported arbitrary-Usize/cMax bound was replaced by that exact raw
input port (no new precondition and no change to A1's target).

Stage 6: NNV_CheckpointDigest.source L046 and NNV_CheckpointValue.source L047
pass, linking the selected digest reply port and erasing the canonical exact
three-query writer execution without evaluating its buffer. This is not the
missing full current writer/flush continuation. NNV_DecodeP1880.native/returned
L048 pass at the SAME decoded statement, retaining original R4 and the
094/087 domains. NNV_WeakErrHost.modelRet1 L049 prints the exact corrected-host
Ok/weak-Err interface; it normalizes the statement and does not prove A1.

No NND_A1 term is delivered. No raw ax2 audit is claimed. The exact remaining
parent and member goals are in NNV_REMAINING.md. The only remaining scope is
NNV_COMBINED_IMPORT (NNH_Run5bCombined plus all accepted NNV proof modules).

Fingerprint labeling note: the own client's inherited
`deps_fingerprint.cache_imports_manifest_sha256` key hashes NNV_PATHS.json,
not a copied cache corpus. Actual imported-object/sidecar hashes are in
`selected_objects`; the Run 5b object pin/recheck manifests agree exactly
(42 files). This job used reference-only seeding as required by the JOB.

Final disposition: no A1 term, no row promotion, no G0/export/manifest replay,
no raw ax2, no Rust/Kani/extraction/ELF job, no shipped-source or trust change.
All work is on codex/cx-a1-20261107, committed by stage; no push. Own objects
remain in the NNV_objects overlay for G0 reuse. Failed sources and exact
errors remain in attempt snapshots; retired drafts are .lean.txt and are
excluded from the combined import. Final evidence validation passes; all
read-only Run 5b object hashes are unchanged.

target not yet established

Continuation stage 1 (new authorization L051-L100): L051 passes
`NNV_FinishCut.returned`, preserving the SAME rounds/claims and finish tail.
No semantic/native association is claimed yet. Own runner budget now admits
only L051-L100 and counts at most 50 new submissions; own receipt/validation
scripts accept the cumulative 100 receipts. Admission, caps, timeout, source
pinning and one-scope rules are unchanged. L052 failed on a missing Std
namespace, corrected in L053; this is a source repair, not a retired heavy shape.

Continuation stage 2: L053 result ports, L054 rounds, L057 record getter,
L063 claims, L064 decoder and L065 prepare-front decomposition pass.
`NNV_PrepareFrontCut.returned` extracts Filled, both expansion outputs, View
and semantic evaluation from the SAME frontValue result. These are canonical
returned-path cuts, not hypotheses about native success. Fixed finish/current
op9 association and the composed A1 remain open. L055/L058/L056/L059/L060/
L061/L062 preserve exact diagnostics; local namespace, abbreviation and Bool
guard repairs are split into subsequent attempts. No cap or heartbeat changed.

Continuation stage 3: L067/L070 close circle projection and the complete SAME
finish-tail decomposition. L068/L069 derive both decode domains from parsed
record provenance. L072/L074-L079 close Filled reservation/value, exact
semantic/values expansion outputs, the current View port, the afterstate
encoder continuation, and the adapter's common source getter. These do not
establish full prepare/body continuation or A1. L066 exposed an obsolete
unqualified S1Semantic import collision; the replacement removes that import
and uses the coherent closure's existing declarations. L071 requires reducing
the canonical front match before rewriting; L073 needs only small natural
reductions. L075 preflight caught a missing private dependency before submission;
the unused import was removed and the same still-unsubmitted attempt admitted
again, without counting that preflight as a Lean scope.

Continuation erasure repair: L080/L081 retain the exact missing
`(PreparedHashCode.run code).2 = PreparedHashCode.erase code` bridge.
The replacement is `NNV_FinishNativePorts`, composing the named `run_value`
law before rounds/circle erasure. The obsolete-import and direct-run/erase
shapes are retired; neither is treated as accepted evidence. L082's terminal
port needs explicit Rust Result constructor qualification in its `change` term.

Continuation stage 4: L083 discharges the native rounds/circle result ports
through named run_value and erasure laws; L084 discharges terminal value
transport with the domain derived from the canonical returned terminal.
L085/L086 pass the source getter/common diagram and exact host op24 encoder.
L088 proves the canonical prepared-return caller yields the SAME semantic,
View and scratch; L089 derives all three buffer lengths symbolically; L090
identifies the actual current query call. No whole dictionary congruence or
whole-buffer normalization is used. L087's flush failure is the elaborated
Vec/Slice rewrite shape; its replacement applies source congruence to the
explicit Result equality instead. Global query/evaluator and A1 are OPEN.

L095 finding: `NNV_CurrentBatchSource` is NOT accepted. Its direct polymorphic
slot projection printed standard axioms, but that projection shape should not
have been used under the retired-shape instruction. The full module used a
VTop digest where Op5T_Install.body requires the stage2 digest, then hit the
200000-heartbeat limit at the source rewrite. No credit, no limit increase,
no unchanged rerun. Retire the draft. A replacement must first use the named
abstract slot projection and an explicitly typed stage2 digest port, then
transport the SAME roots/queries pointwise. This is an unresolved Lean-only
batch association, not a Kani or cryptographic assumption.

L096/L097 replace the failed rewrite shapes with Result congruence. The actual
current flush agrees at the SAME pending/accumulator under its original
LIBC_Finish.Domain; that domain is not yet derived at the full body caller.
The current checkpoint writer agrees with LIBC_Checkpoint.output at the SAME
Prepared/Acc/proof/public inputs and runtime digest replies. The input ports
are closed; whole-body and global weak-Err composition remain open.

Continuation stage 5: L091/L092 compose the actual query carrier inputs;
L093 proves pointwise digest erasure congruence; L096/L097 pass current flush
and checkpoint ports. L099 reflects host encoder Ok back to the SAME owned
source encode call. L098's last goal was already reflexive after case analysis;
the repair is explicit rfl, with no statement or limit change. No global Err
implication is inferred. Unaccepted/unfinished drafts are now .lean.txt and
excluded from the combined import. The 42 read-only Run5b object hashes are
unchanged (NNV_CONTINUATION_PIN_RECHECK.json). The final authorized scope is
NNV_L100, NNV_COMBINED_IMPORT2: original combined import plus 31 new accepted
modules and 45 new printed roots. No A1 term or row credit is delivered.
