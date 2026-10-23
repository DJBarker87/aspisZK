#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys
root=Path(__file__).resolve().parent
m=json.loads((root/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1"
assert m["compiled_objects_included"] is False
source_packet=(root/m["extraction_packet"]).resolve()
assert source_packet.is_file(), f"missing linked extraction packet: {source_packet}"
for row in m["files"]:
 p=root/row["path"]
 assert p.is_file(), f"missing {row['path']}"
 assert p.stat().st_size==row["bytes"], f"size mismatch {row['path']}"
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row["sha256"], f"hash mismatch {row['path']}"
# The Aeneas option cleanup is the only change from generated to normalized files.
for name in ("Types","Funs"):
 raw=(root/f"sources/generated/{name}.lean").read_text()
 norm=(root/f"sources/normalized/{name}.lean").read_text()
 cleaned=raw.replace("\n/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/\nset_option maxHeartbeats 1000000\n\n/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/\nset_option maxRecDepth 2048\n", "")
 assert cleaned==norm, f"unexpected normalization diff in {name}"
assert (root/"sources/coherent/Funs.lean").read_bytes()==(root/"sources/normalized/Funs.lean").read_bytes()
# The named-owner Types source changes only the two discriminant attributes
# into their explicit, reversible read_discriminant definitions and instances.
coherent=(root/"sources/coherent/Types.lean").read_text()
for attr in ("@[discriminant isize]\n",):
 coherent=coherent.replace(attr, "")
for block in (
"""-- Reversible naming-only discriminant expansion reused from stage 2.
def Variant.read_discriminant (x : Variant) : Isize :=
  match x with
  | .S1 => 0#isize
  | .S2 => 1#isize
  | .D => 2#isize

instance _root_.AspisR1S9ActualWeightsNewBoxNewV3.Variant.jointDiscriminant :
    Aeneas.Std.Discriminant Variant Isize where
  read_discriminant := Variant.read_discriminant

""",
"""-- Reversible naming-only discriminant expansion reused from stage 2.
def Error.read_discriminant (x : Error) : Isize :=
  match x with
  | .Allocation => 0#isize

instance _root_.AspisR1S9ActualWeightsNewBoxNewV3.Error.jointDiscriminant :
    Aeneas.Std.Discriminant Error Isize where
  read_discriminant := Error.read_discriminant

"""):
 assert block in coherent
 coherent=coherent.replace(block, "")
coherent=coherent.replace("Visibility: public -/\ninductive Variant where", "Visibility: public -/\n@[discriminant isize]\ninductive Variant where")
coherent=coherent.replace("Visibility: public -/\ninductive Error where", "Visibility: public -/\n@[discriminant isize]\ninductive Error where")
assert coherent==(root/"sources/normalized/Types.lean").read_text()
for stage in ("types","funs"):
 r=json.loads((root/f"proof/{stage}/receipt.json").read_text())
 assert r["exit_status"]==0 and r["process_swaps"]==0
 assert r["source_sha256"]==hashlib.sha256((root/f"sources/coherent/{'Types' if stage=='types' else 'Funs'}.lean").read_bytes()).hexdigest()
# No compiled artifacts or LLBC are permitted in this source packet.
for p in root.rglob("*"):
 if p.is_file():
  assert p.suffix not in {".olean", ".ilean", ".llbc"}, f"unexpected compiled/LLBC artifact: {p}"
print("PASS: named-owner Types/Funs source hashes, reversible option normalization, Funs identity, and green compile receipts; source-only packet")
