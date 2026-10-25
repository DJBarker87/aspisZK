# Stage 1: concrete control-site child on the Uni pair

Checked: SdkD_Uni.accepted_pair_unified, attempt019. It preserves the full
Uni_Accepted conclusion with its SAME existential f,s,cuts. The arbitrary E,
port, FirstMarks and SecondMarks binders are absent. The child is
SdkD_Child.port with E=Unit, a site-only projection of literal source control
execution, not a supplied log. Both typed SDK calls use their actual digest,
semantic/public/proof/checkpoint/hash/observer arguments. All other calls
invoke the installed dictionary directly. All-input Result erasure is proved.

SdkD_First is the existing CurrentCompactCallerModelV1.tx1 body with marks
inserted at its real batch, query and writer calls. The preparation and other
helpers are the original calls, not successful substitutes. SdkD_First.source
checks the complete Result equality. SdkD_FirstOrder derives site order from
that computation on success, with an explicit equation for partial Result
steps. SdkD_Second uses the existing literal VTop_Flow and its typed execution.
SdkD_Marks proves the actual-Ok guarded contracts for all invocation arguments,
including arbitrary observers. No rejected call is forced to have a suffix.

Before: Uni accepted_pair_unified takes port:ChildConeJoin E sdk and both
accepted-only marks. After: SdkD_Uni takes no such inputs; the conclusion uses
let port := SdkD_Child.port adapter current stage finish B std. The quantifier
is specialized from arbitrary payload E/child to this concrete site observer.
All non-child premises and conclusions are retained. No source-equality,
marks, log-success or child-success premise is added. This is a control-site
observation result, not a global digest-log or probability-law refinement.

Ledger delta for this site projection: L088 erasure and Uni-corrected
L089/L090 are supplied by SdkD_Child.erasure and SdkD_Marks.first/second.
No other row is removed; no trust item is added. The full oracle-associated
child obligation and L157/L159 remain open. No credit for authenticated_S1,
global budget/root provenance, arbitrary-payload effects, or the release target.
Replay loss remains 6*(Q+1040)^2/256^32, still uninstantiated security accounting.

Attempts001–019:19 Lean invocations, no dependency rebuild, no Kani, timeout
or memory kill. Attempts001/003/005/006/007/008/010/011/012/013 failed and are
excluded. 007 was missing transitive Port5Q1_Ten on the short search path;
009 uses the inherited full Uni search path with SInt2 first. No launcher or
object infrastructure was changed. Passing objects are new-prefix only.
Only standard axioms in successful sources. Each receipt includes exact
command, revision anchor and dirty source SHA, selected direct object/sidecar
fingerprints, exit, wall, RSS, swaps and complete axioms. Target019: exit0,
2.496790666s,5204696KiB RSS,swap0. Caps6G/8G/Swap0/64,-M7000.

No shipped/cfg(kani) file or frozen artifact changed. Inherited pins remain
as in stage0; no ELF rebuild trigger. No key or other-worker activity.
Next: join Tx2N on the same installed cuts and derive the single recovered map.
