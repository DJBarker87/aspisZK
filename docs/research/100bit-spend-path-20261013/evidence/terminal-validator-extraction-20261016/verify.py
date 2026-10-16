#!/usr/bin/env python3
"""Check exact retained bytes/receipts; this is not a Lean replay."""
from pathlib import Path
import hashlib
import io
import json
import subprocess
import tarfile

b = Path(__file__).resolve().parent
repo = b.parents[4]
sha = lambda data: hashlib.sha256(data).hexdigest()
archive = b / "evidence.tar.gz"
assert sha(archive.read_bytes()) == "ac5326adc42a1e9228a162506538a07bc105940347e7212ae97820e36c87dc36"
with tarfile.open(archive) as t:
    members = {m.name: t.extractfile(m).read() for m in t.getmembers() if m.isfile()}
manifest = json.loads(members["bundle-manifest.json"])
assert set(members) == set(manifest) | {"bundle-manifest.json"}
for name, digest in manifest.items():
    assert sha(members[name]) == digest, name

git_requests = {}
for stage in ["before", "final", "helper"]:
    pins = json.loads(members[f"{stage}/input/source-pins.json"])
    for name, digest in pins["kit_files"].items():
        git_requests[f"{pins['source_revision']}:{name}"] = digest
        archived = f"{stage}/input/{name}"
        if archived in members:
            assert sha(members[archived]) == digest, archived
raw = subprocess.check_output(
    ["git", "cat-file", "--batch"], cwd=repo,
    input=("\n".join(git_requests) + "\n").encode())
stream = io.BytesIO(raw)
for request, digest in git_requests.items():
    header = stream.readline().decode().split()
    assert len(header) == 3 and header[1] == "blob", (request, header)
    data = stream.read(int(header[2]))
    assert stream.read(1) == b"\n"
    assert sha(data) == digest, request
assert stream.read() == b""

failures = {"final/runs/aeneas-a/receipt.json", "helper/runs/aeneas-b/receipt.json"}
receipts = [name for name in members if name.endswith("/receipt.json")]
for name in receipts:
    r = json.loads(members[name])
    assert r["exit_status"] == (2 if name in failures else 0), name
    assert r["limits"] == {"memory.high": "6442450944", "memory.max": "8589934592", "memory.swap.max": "0"}
    assert r["swaps"] == 0 and r["wall_seconds"] < 600, name
    assert r["runner_sha256"] == sha(members[name.split("/")[0] + "/run-host.py"])
    assert r["source_revision"] == json.loads(members[name.split("/")[0] + "/input/source-pins.json"])["source_revision"]
    assert all(int(line.split()[1]) == 0 for line in r["memory_events"].splitlines()), name
traces = [members[f"{stage}/runs/trace-a/stdout.log"] for stage in ["before", "final", "helper"]]
assert traces[0] == traces[1] == traces[2]
assert traces[0].splitlines()[-1] == b"complete 1233"
translation = json.loads(members["helper/extraction-c/generated/translation.json"])
opaque = [x for x in translation["functions"] if x.get("is_opaque")]
assert len(opaque) == 1 and opaque[0]["lean_name"] == "AspisR1TerminalValidator.Slice.Insts.CoreCmpPartialEqArray.eq"
for key in ["types", "globals"]:
    assert not [x for x in translation.get(key, []) if x.get("is_opaque")], key
for name in ["Types.lean", "Funs.lean"]:
    data = members["helper/extraction-c/generated/AspisR1TerminalValidator/" + name]
    assert b"CoreCmpPartialEqArray" not in data
    assert b"axiom " not in data and b"sorry" not in data
    mirror = repo / "docs/research/100bit-spend-path-20261013/lean/extracted-terminal-validator-20261016/AspisR1TerminalValidator" / name
    assert mirror.read_bytes() == data
print(f"PASS: {len(manifest)} archive hashes, {len(git_requests)} source pins, {len(receipts)} tool/native receipts, 1233 equal traces; Lean closure audited separately")
