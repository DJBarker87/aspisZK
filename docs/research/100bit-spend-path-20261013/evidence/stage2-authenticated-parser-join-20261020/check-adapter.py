from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent
repo=next(x for x in p.parents if (x/".git").exists())
pins=json.loads((p/"discriminant-adapter-pins.json").read_text())
old=repo/"docs/research/100bit-spend-path-20261013/evidence/stage2-parse-variant-tag-20261019/sources/AspisR1Stage2AdoptedParseShape/Types.lean"
raw=old.read_text();assert hashlib.sha256(raw.encode()).hexdigest()==pins["original_sha256"]
out=raw
for before,after in pins["blocks"]:
 assert out.count(before)==1;out=out.replace(before,after,1)
assert out==(p/"sources/AspisR1Stage2AdoptedParseShape/Types.lean").read_text()
for before,after in reversed(pins["blocks"]):out=out.replace(after,before,1)
assert out==raw
for name in ["Stage2ParseShapeExplicitOps","Stage2ParseShapeSuccess"]:
 src=old.parents[1]/(name+".lean")
 assert src.read_bytes()==(p/"sources"/(name+".lean")).read_bytes()
print("PASS: names-only discriminant expansion; exact parser and success-proof bodies retained")
