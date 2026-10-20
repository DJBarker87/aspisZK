# Record-class packet

Parent revision: f47037375f1b02492aee023616ed4c553a16d8d4.

Final sources: WireBindingRecordCodec (13150a7edb60...), BinWireBindingLengths
(f71fc1411ad7...), R1Z.WireBindingLengthsR1PBin (ce417ae7ce0d...). The shared
codec is uploaded verbatim from the soundness tree to J's sources root.

Local commands are in each receipt and use the mkdir lock, own object directory,
-j1 -M4400 -DElab.async=false, /usr/bin/time -l. Source snapshots, complete
axiom output, errors and timing are retained per attempt. Only final successes
are claimed. The final manifest contains source hashes, direct object hashes,
object sizes, revision, timings, RSS, swaps and axiom reports. No objects are
committed. The audit reads receipts and hashes; it never replays Lean.

History: the initial arithmetic/ASCII-list codec and both consumers compiled.
Tightening the domain to the literal source string first failed at an attempted
rfl equality with ByteArray.toList, then at a missing Nat induction import.
The final source instead uses a symbolic ByteArray length lemma and the minimal
Nat import. These were elaboration failures, not memory failures or false
mathematical targets. Failed logs may contain Lean-generated sorryAx audit
lines; final audits do not. No caps were raised.

One unchanged local BinWireBindingLengths replay occurred while adding the
runner's dependency-fingerprint guard, before the tightened codec compiled.
It was redundant and is retained in the manifest (wall 9.880 s). The guard now
compares source plus hashes of direct imports, including receipts predating
its explicit fingerprint field. The final dependent replay followed the
successful source change and uses the new codec object.

J 6300/6301 are successful historical ASCII-list codec/privacy builds;
6302/6303 are the final literal-domain codec and dependent replay. All were
run through run-joint.sh, J, -M7000, MemoryMax 7G, MemoryHigh 5G,
MemorySwapMax 0; its reservation/serialization controls were retained.
No other attempt numbers were used. `j-attempts.jsonl` is copied from the
worker log, also appended on J to shared evidence/attempts.jsonl. `J/` holds
full out/time logs. `j-dependencies.json` resolves package/core imports that
the inherited launcher's J-object-only fingerprint algorithm labels missing.
It also pins the unchanged privacy roots; these do not import the new module.

Before replacing the new shared codec source/object and rebuilding its privacy
dependent, prior artifacts were copied to the branch-named directory
/home/dombarker/project-offloads/codex-cx-record-classes-20261020/snapshots/.
No preexisting shared module was replaced. No full manifest, unchanged root,
Rust build or runtime suite was replayed.
