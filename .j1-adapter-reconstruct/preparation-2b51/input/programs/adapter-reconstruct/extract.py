#!/usr/bin/env python3
"""Cut four adapter functions and their structural carrier without rewriting bodies."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

REVISION = "2b51d49959741f238894bdd5dd069cf90a366e58"
SOURCE = "programs/r1-cost-probe/src/r1_pool_adapter.rs"
NAMES = ["AuthenticatedAsq8Accounts", "asq8_common", "transfer_statement_box",
         "withdrawal_statement_box", "reconstruct_asq8_statement"]
HEADER = """// Generated exact declaration cut; see source-pins.json.
extern crate alloc;

#[cfg(feature = "pool-adapter")]
mod r1_pool_adapter {
use alloc::boxed::Box;
use solana_program_error::ProgramError;
use aspis_statement::pool_v1::{
    PoolV1PairForestMasterV1, PoolV1PairForestCheckpointV1,
    PoolV1PairForestLaneStateV1, PoolV1PairLiveSnapshotV1,
    PoolV1PairForestTerminalCommonV1, PoolV1PairLatePublicStatementV1,
    PoolV1PairForestTerminalStatementV1, PoolV1PairForestTerminalPaymentV1,
    PoolV1PairForestTerminalRequestV1,
    validate_pool_v1_pair_forest_terminal_statement_v1,
};

"""
MANIFEST = """[package]
name = "aspis-r1-adapter-reconstruct"
version = "0.1.0"
edition = "2021"
publish = false

[lib]
path = "lib.rs"

[features]
default = []
pool-adapter = []
private-leaf-salts = []

[dependencies]
aspis-statement = { path = "../../crates/aspis-statement", features = ["r0", "pool-v1-kernel"] }
solana-program-error = { version = "=2.2.2", features = ["serde", "borsh"] }
"""

def sha(data):
    return hashlib.sha256(data).hexdigest()

def blob(repo, path):
    return subprocess.check_output(["git", "-C", str(repo), "show", REVISION + ":" + path])

def cut(text, name):
    matches = list(re.finditer(r"(?m)^(?:struct|fn) " + re.escape(name) + r"\b", text))
    assert len(matches) == 1, name
    start = matches[0].start()
    if text[:start].endswith("#[inline(never)]\n"):
        start -= len("#[inline(never)]\n")
    opening = text.index("{", matches[0].start())
    # These five exact declarations contain no braces in comments or strings.
    depth = 1
    end = opening + 1
    while depth:
        if text[end] == "{": depth += 1
        elif text[end] == "}": depth -= 1
        end += 1
    selected = text[start:end] + "\n"
    assert not re.search(r'//|/\*|"', selected), name
    return selected, text[:start].count("\n") + 1, text[:end].count("\n") + 1

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    source = blob(a.repo, SOURCE)
    chunks, records = [], []
    for name in NAMES:
        text, first, last = cut(source.decode(), name)
        chunks.append(text)
        records.append({"name": name, "start_line": first, "end_line": last,
                        "sha256": sha(text.encode())})
    lib = (HEADER + "\n".join(chunks) + "\n}\n").encode()
    pins = {"source_revision": REVISION, "source_path": SOURCE,
            "source_sha256": sha(source), "cuts": records,
            "lib_sha256": sha(lib), "manifest_sha256": sha(MANIFEST.encode()),
            "admitted_feature_context": ["pool-adapter", "private-leaf-salts"],
            "cut_feature_limit": "Only pool-adapter gates this module; all five source declarations are otherwise cfg-independent. The cut omits verifier execution and is not a full program build.",
            "import_adjustment": "ProgramError resolves directly to the same solana-program-error 2.2.2 type reexported by solana-program 2.3.0; no replacement enum.",
            "open": ["Account authentication/constructor provenance", "Rust/compiler execution preservation", "PDA/runtime/custody semantics"]}
    outputs = {"lib.rs": lib, "Cargo.toml": MANIFEST.encode(),
               "source-pins.json": (json.dumps(pins, indent=2, sort_keys=True) + "\n").encode()}
    if a.check:
        for name, data in outputs.items():
            assert (a.out/name).read_bytes() == data, name
    else:
        a.out.mkdir(parents=True, exist_ok=True)
        for name, data in outputs.items(): (a.out/name).write_bytes(data)
    print(json.dumps({"checked": a.check, "cuts": len(records), "rust_lines": lib.count(b"\n"),
                      "lib_sha256": sha(lib), "revision": REVISION}))

if __name__ == "__main__":
    main()
