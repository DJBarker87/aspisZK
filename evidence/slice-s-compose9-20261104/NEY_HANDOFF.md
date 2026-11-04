# NEY live continuation checkpoint

Work remains active. This file is provisional until the final validator,
stop audit and receipt inventory are written. Target not yet established.

Branch codex/cx-slice-s-compose9-20261104; requested worktree and branch were
already at the November4 continuation tip f50f155efa4. Preserve this branch.
Only NEY-prefixed files under this evidence directory change. No push, shipped
file change, wallet operation or ELF rebuild occurred.

Baseline NEX82/97 rows,93/129 edges,2/7 roots is fully replayed. Terminal native
checks K001–052 observe one field at a time, with full child Results, actual
pointer/argument/order checks and matched controls. Controls for recipient,
amount and destination are restricted to their active enum variant; positives
are unrestricted. K053 tests the wrong payment slice. Public root K054–105
covers26 fields; K106/K107 test wrong allocation and child reply. No native
credit is inferred from partial sets.

Accepted Lean checks: L002 result-window KMX composition/frame; L004 total
binding continuation; L005/L006 and L009–032 the26 exact field-coordinate
alignments; L007 binding success establishes same-input statement success;
L008 complete emitted result-encoder substitution. All have standard axioms
only. L001/L003 failed elaboration and remain excluded. Native proofs use the
exact KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.

Private source validation now independently reconstructs every compiled frozen
source from git blobs plus exact approved KMX/control/NEY patches. Earlier
receipts are checked retroactively; new runners check before launch. This
strengthens validation without changing host infrastructure or rerunning proofs.

Host workspace /home/dombarker/project-offloads/codex-cx-slice-s-compose9-20261029.
Private retained cache /home/dombarker/project-offloads/codex-cx-slice-s-compose9-cache-20261029.
NEX accepted objects were copied first; imported hashes are in NEY_HOST_PINS.json.
Lean resolves own new objects, retained NEX archive, predecessor archives/cache,
and coherent SInt2; each receipt pins selected objects and Aeneas objects.
One capped scope at a time; exact6G/8G/Swap0/Tasks64 and Lean-M7000; optimized
Rust, frozen graph/offline lock checks and post-run lock stability required.

Active local controllers: terminal campaign PID30852 and continuation PID64851
(see controller-pause JSONs). They have been resumed; only controllers, never
provers, were paused for Lean checks. NEY_continue.py waits for K052 completion,
then runs the public and remaining campaigns sequentially. Do not resubmit an
in-flight attempt. Check NEY_ACTIVE.json and recovered receipts first.

Budget150 Kani/60 Lean. The residual plan is NEY_REMAINING_PLAN.md. Stage code
validates complete sets and commits automatically after terminal/public stages.
No unrelated OPEN member holds the next independent check. All remaining
obligations must be reported individually after the final allowance is used.

The native principle is ruling(y) hybrid composition, with source erasure,
complete typed child Results, same arguments/carriers/state and ordered effects,
then existing Lean substitution/domain/extensionality. P6/D188 optionA is
reclassification. RuntimeReturnData under(ab) is ADDED trust, currently no
newly CLOSED use. Root conditions remain own PacketDomain/PhysicalInterpretation,
approved trust rows and RuntimePersistence. Headline/frozen3/L154/D188 and the
100-bit per-attempt/privacy/two-transaction contract remain unchanged.
