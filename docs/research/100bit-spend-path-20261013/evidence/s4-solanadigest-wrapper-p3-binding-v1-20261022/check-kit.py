#!/usr/bin/env python3
"""Validate the focused SolanaDigest source cut and pinned dependency bodies."""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPO = Path("/Users/dominic/ZK")
PIN = json.loads((ROOT / "source-pins.json").read_text())

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(f"FAIL: {message}")

prod = (REPO / "programs/r1-cost-probe/src/lib.rs").read_bytes()
trait = (REPO / "crates/aspis-core/src/digest.rs").read_bytes()
transcript = (REPO / "crates/aspis-core/src/transcript.rs").read_bytes()
snap = ROOT / "source-snapshots"
cut = (ROOT / "input/lib.rs").read_bytes()
lock = (ROOT / "input/Cargo.lock").read_bytes()
trait_cut = (ROOT / "input/aspis-core/src/digest.rs").read_bytes()

require(sha(prod) == PIN["production_lib_sha256"], "production lib.rs source pin")
require(sha(trait) == PIN["aspis_core_digest_trait_sha256"], "Digest32 trait source pin")
frag = prod[PIN["production_fragment_start_byte"]:PIN["production_fragment_end_byte_exclusive"]]
require(sha(frag) == PIN["production_fragment_sha256"], "production wrapper fragment pin")
require(frag in cut, "candidate must contain exact production wrapper bytes")
require((snap / "production-lib.rs").read_bytes() == prod, "production source snapshot")
require((snap / "aspis-core-digest.rs").read_bytes() == trait, "Digest32 source snapshot")
require(sha(transcript) == PIN["aspis_core_hashfn_alias_source_sha256"],
        "HashFn alias source pin")
require((snap / "aspis-core-transcript.rs").read_bytes() == transcript,
        "HashFn alias source snapshot")
require(trait_cut == trait, "isolated trait cut is byte-identical to actual Digest32 source")
cut_root = (ROOT / "input/aspis-core/src/lib.rs").read_text()
require("pub type HashFn = fn(&[&[u8]]) -> [u8; 32];" in transcript.decode(),
        "actual transcript HashFn alias")
require(cut_root.startswith("#![no_std]\npub type HashFn = fn(&[&[u8]]) -> [u8; 32];\n"),
        "isolated crate root carries exact HashFn alias needed by retained Digest32 source")
require(sha((ROOT / "input/aspis-core/src/lib.rs").read_bytes()) ==
        PIN["isolated_aspis_core_lib_sha256"], "isolated crate-root pin")
require(sha(lock) == PIN.get("candidate_cargo_lock_sha256"), "candidate Cargo.lock pin")
lock_text = lock.decode()
for name, version, checksum in (
    ("solana-program", "2.3.0", "98eca145bd3545e2fbb07166e895370576e47a00a7d824e325390d33bf467210"),
    ("solana-hash", "2.3.0", "b5b96e9f0300fa287b545613f007dfe20043d7812bee255f418c1eb649c93b63"),
    ("solana-sha256-hasher", "2.3.0", "5aa3feb32c28765f6aa1ce8f3feac30936f16c5c3f7eb73d63a5b8f6f8ecdc44"),
):
    block = re.search(rf'(?ms)^name = "{re.escape(name)}"\n.*?(?=^\[\[package\]\]|\Z)', lock_text)
    require(block is not None and f'version = "{version}"' in block.group(0)
            and f'checksum = "{checksum}"' in block.group(0), f"Cargo.lock exact pin for {name}")
require('solana-program = "=2.3.0"' in (ROOT / "input/Cargo.toml").read_text(),
        "candidate depends on exact Solana program version")
require('aspis-core = { path = "aspis-core" }' in (ROOT / "input/Cargo.toml").read_text(),
        "candidate points to the exact local trait source cut")

text = cut.decode()
require(text.startswith("#![no_std]\n"), "no_std source cut")
require(text.count("hashv(parts).to_bytes()") == 1, "exactly one retained hashv/to_bytes call")
require("pub fn digest_probe(parts: &[&[u8]]) -> [u8; 32]" in text, "probe root exists")
require("struct SolanaDigest;" in text and "impl aspis_core::Digest32 for SolanaDigest" in text,
        "actual wrapper type/impl retained")
require("fn digest(&self, parts: &[&[u8]]) -> [u8; 32]" in trait.decode(), "trait signature")
require(sha((ROOT / "source-snapshots/solana-hash-2.3.0-lib.rs").read_bytes()) ==
        PIN["cargo_registry_source"]["solana_hash_lib_sha256"], "solana-hash source snapshot pin")
require(sha((ROOT / "source-snapshots/solana-sha256-hasher-2.3.0-lib.rs").read_bytes()) ==
        PIN["cargo_registry_source"]["solana_sha256_hasher_lib_sha256"], "sha256-hasher source snapshot pin")
require(sha((ROOT / "source-snapshots/solana-program-2.3.0-hash.rs").read_bytes()) ==
        PIN["cargo_registry_source"]["solana_program_hash_module_sha256"], "solana-program hash re-export source snapshot pin")

hash_src = (snap / "solana-hash-2.3.0-lib.rs").read_text()
hasher_src = (snap / "solana-sha256-hasher-2.3.0-lib.rs").read_text()
require("#[derive(Clone, Copy, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]" in hash_src,
        "actual Hash Copy derive")
require("pub struct Hash(pub(crate) [u8; HASH_BYTES]);" in hash_src, "transparent 32-byte Hash representation")
require("pub fn to_bytes(self) -> [u8; HASH_BYTES] {\n        self.0\n    }" in hash_src,
        "actual Hash::to_bytes body")
require("pub fn hashv(vals: &[&[u8]]) -> Hash" in hasher_src, "actual hashv signature")
require("sol_sha256(" in hasher_src and "self.hasher.update(val)" in hasher_src,
        "hashv source explicitly shows platform syscall and host concatenation paths")

for p in ROOT.rglob("*"):
    if p.is_file() and (p.suffix in {".olean", ".ilean", ".rlib", ".rmeta", ".so", ".dylib"}
                        or p.name in {"charon", "main.exe"}):
        raise SystemExit(f"FAIL: generated/binary artifact in source kit: {p.relative_to(ROOT)}")

print("PASS: exact production wrapper, Digest32 trait, pinned Hash Copy/to_bytes body, hashv boundary, and source-only kit")
