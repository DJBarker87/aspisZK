#!/usr/bin/env python3
"""Read-only V403 source inventory at the requested immutable candidate."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
REV = subprocess.check_output(
    ["git", "rev-parse", "d4ed1ba89f0^{commit}"], text=True).strip()


def source(path):
    return subprocess.check_output(["git", "show", f"{REV}:{path}"], text=True)


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


# Ignore braces in strings/comments when locating the enclosing Rust function.
TOKEN = re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|\bfn\s+([A-Za-z_][A-Za-z_0-9]*)|[{}]', re.S)


def enclosing(text, offset):
    stack = []
    pending = None
    for token in TOKEN.finditer(text):
        if token.start() >= offset:
            break
        if token.group(1):
            pending = token.group(1)
        elif token.group() == "{":
            stack.append(pending)
            pending = None
        elif token.group() == "}":
            if stack:
                stack.pop()
    return next((name for name in reversed(stack) if name), None)


paths = subprocess.check_output(
    ["git", "grep", "-l", "evaluate_state_only_polynomial", REV, "--",
     "crates", "programs", "tools/r1-cost-probe"], text=True).splitlines()
calls = []
sources = {}
for item in paths:
    path = item.split(":", 1)[1]
    text = source(path)
    sources[path] = sha(text)
    for hit in re.finditer(r"\bevaluate_state_only_polynomial\s*\(", text):
        before = text[:hit.start()]
        # Function definitions are the two target items, not caller events.
        if re.search(r"\bfn\s*$", before):
            continue
        calls.append({"path": path, "line": before.count("\n") + 1,
                      "function": enclosing(text, hit.start()),
                      "source_line": text.splitlines()[before.count("\n")]})

producer_paths = [
    "crates/aspis-core/src/field.rs", "crates/aspis-core/src/field/ct.rs",
    "crates/aspis-core/src/transcript.rs", "crates/aspis-core/src/v6_onefold.rs",
    "crates/aspis-core/src/state_only_prefix.rs", "crates/aspis-prover/src/v5_mask.rs",
    "crates/aspis-core/src/r0_transcript.rs",
    "crates/aspis-r1-cost-probe/src/host_sumcheck.rs",
    "crates/aspis-r1-cost-probe/src/host_semantic.rs",
    "crates/aspis-r1-cost-probe/src/r1_wire.rs",
    "crates/aspis-r1-cost-probe/src/sampler.rs",
    "crates/aspis-r1-cost-probe/src/host_work.rs",
    "docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs",
]
definitions = []
for path in producer_paths:
    text = source(path)
    sources[path] = sha(text)
    for line, body in enumerate(text.splitlines(), 1):
        if re.search(r"\bfn\s+[A-Za-z_]|pub struct M31|pub const P:", body):
            definitions.append({"path": path, "line": line, "declaration": body.strip()})

result = {"candidate_revision": REV,
          "search_scope": ["crates", "programs", "tools/r1-cost-probe"],
          "method": "textual direct-call census, then manual import/cfg classification in INVENTORY.md; not a reachability proof",
          "calls": calls, "producer_and_transport_definitions": definitions,
          "source_sha256": dict(sorted(sources.items()))}
(HERE / "inventory.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"candidate_revision": REV, "direct_calls": len(calls),
                  "source_files": len(sources)}, sort_keys=True))
