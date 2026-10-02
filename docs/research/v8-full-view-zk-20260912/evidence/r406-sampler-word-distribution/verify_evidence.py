#!/usr/bin/env python3
"""Read-only verification of saved R406 source/build evidence."""
from pathlib import Path
import hashlib, json, re, sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
TARGET = ROOT / "docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R406SamplerWordDistribution.lean"
EXPECTED = {
    "1790961087849355000": (1, "0:05.66", 3213568),
    "1790961454185659000": (1, "0:01.49", 3218684),
    "1790961498739365000": (0, "0:01.56", 3232976),
}
EXPECTED_SOURCE = "b7b3aa0f3f42e39ce5945f3d4bdaad7544f2dfd39292ecf0bc26b9ea9eac1ed9"
NAMES = ["word_value", "masked_value", "words_value", "uniform_candidates"]
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok, msg):
    if not ok: raise AssertionError(msg)

require(TARGET.is_file() and sha(TARGET) == EXPECTED_SOURCE, "promoted source hash mismatch")
require(sha(HERE / "R406SamplerWordDistribution.lean") == EXPECTED_SOURCE, "evidence source hash mismatch")
require((HERE / "R406SamplerWordDistribution.lean").read_bytes() == TARGET.read_bytes(), "promoted/evidence source bytes differ")
receipt_list=[]
for rid, (status, wall, rss) in EXPECTED.items():
    stem=f"aspis-focus-{rid}"
    receipt=json.loads((HERE/"runs"/(stem+".receipt.json")).read_text())
    log=(HERE/"runs"/(stem+".log")).read_text()
    source=HERE/"runs"/(stem+".source.lean")
    require(receipt["exit_status"]==status, f"{rid}: status")
    require(receipt["wall_time"]==wall, f"{rid}: wall")
    require(receipt["peak_rss_kib"]==rss, f"{rid}: RSS")
    require(receipt["swaps"]==0, f"{rid}: swap")
    require(receipt["resources"]=={"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":0,"TasksMax":128,"lean_flags":"-j1 -M4500"}, f"{rid}: resource cap")
    require(receipt["runner_sha256"]=="d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea", f"{rid}: runner hash")
    require(receipt["source_revision"]=="d473563212029be91ea1032bfd2ef70ee6d68b73", f"{rid}: source revision")
    require(sha(source)==receipt["source_sha256"], f"{rid}: captured input hash")
    require("Exit status: "+str(status) in log, f"{rid}: exact exit in log")
    require("Swaps: 0" in log, f"{rid}: log swap")
    require("Elapsed (wall clock) time (h:mm:ss or m:ss): "+wall in log, f"{rid}: raw log wall")
    require("Maximum resident set size (kbytes): "+str(rss) in log, f"{rid}: raw log RSS")
    parsed=re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)
    require(parsed==receipt["complete_print_axioms"], f"{rid}: all raw axiom reports match receipt")
    if status:
        require("sorryAx" in log and all("sorryAx" in a for a in receipt["complete_print_axioms"]), f"{rid}: failure/sorryAx retained")
    else:
        expected=[f"'AspisV8R19.R406SamplerWordDistribution.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in NAMES]
        require(receipt["complete_print_axioms"]==expected, "final complete axiom report mismatch")
        for line in expected: require(line in log, "final axiom missing from log: "+line)
        require("sorryAx" not in log, "final log contains sorryAx")
    receipt_list.append({"id":rid,"exit_status":status,"wall_time":wall,"peak_rss_kib":rss,"swaps":0,"source_sha256":receipt["source_sha256"]})
require(sha(HERE/"runner/run_focus.py")=="d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea", "runner copy mismatch")
for name, h in {"SamplerWords.lean":"21f5742355920ce7f6a70496e6255e8d50d10739a75b8a5671030eea6fb1dbb9", "OracleResampling.lean":"52bfa930954dc2a04fc43d0266e0af6900c5099de1d43758789170fa6077c536"}.items():
    require(sha(HERE/"dependencies"/name)==h, "direct dependency source hash mismatch: "+name)
cache=json.loads((HERE/"dependency-cache-identities.json").read_text())
for module, item in cache["mathlib_modules"].items():
    require(sha(HERE/item["saved_source"])==item["source_sha256"], "Mathlib source mismatch: "+module)
    require(item["saved_source_actual_sha256"]==item["source_sha256"], "Mathlib source manifest mismatch: "+module)
# Verify root inventory hashes, excluding exactly the root checksum file.
files_index=json.loads((HERE/"FILES.json").read_text())
expected_file_paths=sorted(p.relative_to(HERE).as_posix() for p in HERE.rglob("*") if p.is_file() and p.name not in {"FILES.json","SHA256SUMS"})
require(files_index["files"]==expected_file_paths, "FILES.json inventory mismatch")
for line in (HERE/"SHA256SUMS").read_text().splitlines():
    digest, rel=line.split("  ",1)
    p=HERE/rel
    require(rel!="SHA256SUMS" and p.is_file() and sha(p)==digest, "saved checksum mismatch: "+rel)
listed={line.split("  ",1)[1] for line in (HERE/"SHA256SUMS").read_text().splitlines()}
actual={p.relative_to(HERE).as_posix() for p in HERE.rglob("*") if p.is_file() and p.name!="SHA256SUMS"}
require(listed==actual, "checksum inventory is incomplete or has extra paths")
print(json.dumps({"status":"pass","target_sha256":EXPECTED_SOURCE,"runs":receipt_list,"axiom_names":NAMES,"foundation_set":sorted(FOUNDATIONS),"checked_files":len(actual)},indent=2))
