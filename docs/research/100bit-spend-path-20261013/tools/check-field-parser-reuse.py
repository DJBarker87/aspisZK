#!/usr/bin/env python3
"""Read-only check of current and historical aspic-core field parser bodies."""

from __future__ import annotations

import hashlib
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[4]
FIELD = "crates/aspis-core/src/field.rs"
REVISIONS = {
    "pinned_current": "8b62ca762b89b5af8f131d1c97a5c6d400df2a6b",
    "R492": "d1d92d62a244732bc9ecf742e79fc05c7229ac5b",
    "R567": "6742daddf92657fee803c56f353415b9a882e8ff",
}
FULL_SOURCE_SHA256 = {
    "pinned_current": "3046536d04e84357c7df7bd742ec9839d1e1dc47ccc0ecaa59eb79ddec453c68",
    "R492": "5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8",
    "R567": "5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8",
}
FUNCTIONS = {
    "M31::from_le_bytes": (
        "pub fn from_le_bytes(bytes: [u8; 4]) -> Option<M31>",
        "61801dea89bcc6f411c3b373fcf966d9f257f4ca5b251f4b896c1c428c1102b7",
    ),
    "CM31::from_le_bytes": (
        "pub fn from_le_bytes(bytes: &[u8]) -> Option<CM31>",
        "b291b31b3aba3ab9ff3812e98f3d774577e69bba3cba57392d9bcb255d0a5f0b",
    ),
    "QM31::from_le_bytes": (
        "pub fn from_le_bytes(bytes: &[u8]) -> Option<QM31>",
        "3e58a8f03ca2ece6801dbfee02fa6b119fcde8c9f3240ab4f0c5e9e0e2b22a56",
    ),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def function_body(source: str, signature: str) -> str:
    """Return signature through the matching closing brace for these functions."""
    if source.count(signature) != 1:
        raise ValueError(f"expected exactly one signature occurrence: {signature}")
    start = source.index(signature)
    opening = source.index("{", start)
    depth = 0
    for i in range(opening, len(source)):
        if source[i] == "{":
            depth += 1
        elif source[i] == "}":
            depth -= 1
            if depth == 0:
                return source[start : i + 1]
    raise ValueError(f"unclosed function body: {signature}")


def source_at(revision: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{revision}:{FIELD}"], cwd=ROOT)


def main() -> int:
    sources = {name: source_at(revision) for name, revision in REVISIONS.items()}
    sources["working-tree"] = (ROOT / FIELD).read_bytes()
    for name, raw in sources.items():
        actual = sha256(raw)
        pinned = FULL_SOURCE_SHA256.get(name)
        if pinned is not None and actual != pinned:
            print(f"{name}: full-source hash mismatch: {actual}", file=sys.stderr)
            return 1
        print(f"{name} full field.rs sha256 {actual}")
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    print(f"actual HEAD {head} (comparison uses pinned git references, not HEAD equality)")

    decoded = {name: raw.decode("utf-8") for name, raw in sources.items()}
    for label, (signature, expected) in FUNCTIONS.items():
        hashes = {
            name: sha256(function_body(source, signature).encode("utf-8"))
            for name, source in decoded.items()
        }
        if any(value != expected for value in hashes.values()):
            print(f"{label}: parser-body mismatch: {hashes}", file=sys.stderr)
            return 1
        print(f"{label} parser-body sha256 {expected}; identical at all four sources")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
