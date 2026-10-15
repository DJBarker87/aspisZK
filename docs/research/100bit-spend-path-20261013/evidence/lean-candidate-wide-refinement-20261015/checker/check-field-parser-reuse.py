#!/usr/bin/env python3
"""Check pinned historical field parsers or the isolated parser candidate."""

from __future__ import annotations

import hashlib
import io
import subprocess
import sys
import tarfile
import tempfile
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
CANDIDATE_SOURCE_SHA256 = "28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea"
CANDIDATE_EVIDENCE = Path(
    "docs/research/100bit-spend-path-20261013/evidence/field-parser-candidate-20261014"
)
CANDIDATE_ARCHIVE = "field-parser-candidate-attempt-a.tar.gz"
CANDIDATE_ARCHIVE_SHA256 = "06ccb4223dd30af6d62bcaf3c5c8b74ee384bfad95d6731017486e5de052e1d4"
CANDIDATE_MEMBER = "attempts/a/source/field.rs"
CANDIDATE_PATCH_MEMBER = "candidate-input/explicit-result-match.patch"
CANDIDATE_PATCH_SHA256 = "f048cad49748468db3b1732b1a1e7f74560a8a029c7b0b1c5815912b92a87ac5"
BASELINE_SOURCE_SHA256 = FULL_SOURCE_SHA256["pinned_current"]
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


def archive_member(archive_path: Path, member_name: str, expected_hash: str) -> bytes:
    raw_archive = archive_path.read_bytes()
    archive_hash = sha256(raw_archive)
    if archive_hash != CANDIDATE_ARCHIVE_SHA256:
        raise ValueError(f"candidate archive hash mismatch: {archive_hash}")
    with tarfile.open(fileobj=io.BytesIO(raw_archive), mode="r:gz") as archive:
        member = archive.extractfile(member_name)
        if member is None:
            raise ValueError(f"candidate archive member missing: {member_name}")
        raw = member.read()
    actual = sha256(raw)
    if actual != expected_hash:
        raise ValueError(f"candidate archive member hash mismatch ({member_name}): {actual}")
    return raw


def apply_candidate_patch(baseline: bytes, patch: bytes) -> bytes:
    """Apply the pinned patch to a temporary copy of the pinned baseline."""
    with tempfile.TemporaryDirectory(prefix="field-parser-reuse-") as temp_dir:
        repo = Path(temp_dir)
        target = repo / FIELD
        target.parent.mkdir(parents=True)
        target.write_bytes(baseline)
        subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
        subprocess.run(["git", "apply", "--check", "-"], cwd=repo, input=patch, check=True)
        subprocess.run(["git", "apply", "-"], cwd=repo, input=patch, check=True)
        return target.read_bytes()


def main() -> int:
    sources = {name: source_at(revision) for name, revision in REVISIONS.items()}
    sources["working-tree"] = (ROOT / FIELD).read_bytes()

    candidate_root = ROOT / CANDIDATE_EVIDENCE
    try:
        candidate_source = archive_member(
            candidate_root / CANDIDATE_ARCHIVE,
            CANDIDATE_MEMBER,
            CANDIDATE_SOURCE_SHA256,
        )
        candidate_patch = archive_member(
            candidate_root / CANDIDATE_ARCHIVE,
            CANDIDATE_PATCH_MEMBER,
            CANDIDATE_PATCH_SHA256,
        )
        patched_baseline = apply_candidate_patch(sources["pinned_current"], candidate_patch)
    except (OSError, ValueError, subprocess.CalledProcessError, tarfile.TarError) as error:
        print(f"candidate evidence check failed: {error}", file=sys.stderr)
        return 1
    if sha256(candidate_source) != CANDIDATE_SOURCE_SHA256:
        print("candidate full-source hash mismatch", file=sys.stderr)
        return 1
    if patched_baseline != candidate_source:
        print("pinned candidate patch output differs from archived candidate source", file=sys.stderr)
        return 1

    working_hash = sha256(sources["working-tree"])
    if working_hash == BASELINE_SOURCE_SHA256:
        working_variant = "historical-baseline"
    elif working_hash == CANDIDATE_SOURCE_SHA256:
        working_variant = "isolated-candidate"
        if sources["working-tree"] != candidate_source:
            print("working candidate differs from pinned archive source", file=sys.stderr)
            return 1
    else:
        print(f"working-tree full-source hash is not an allowed variant: {working_hash}", file=sys.stderr)
        return 1
    sources["candidate-archive"] = candidate_source

    for name, raw in sources.items():
        actual = sha256(raw)
        pinned = FULL_SOURCE_SHA256.get(name)
        if name == "working-tree" and working_variant == "isolated-candidate":
            pinned = CANDIDATE_SOURCE_SHA256
        elif name == "candidate-archive":
            pinned = CANDIDATE_SOURCE_SHA256
        if pinned is not None and actual != pinned:
            print(f"{name}: full-source hash mismatch: {actual}", file=sys.stderr)
            return 1
        print(f"{name} full field.rs sha256 {actual}")
    print(f"working-tree variant {working_variant}")
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    print(f"actual HEAD {head} (comparison uses pinned git references, not HEAD equality)")

    decoded = {name: raw.decode("utf-8") for name, raw in sources.items()}
    for label in ("M31::from_le_bytes", "QM31::from_le_bytes"):
        signature, expected = FUNCTIONS[label]
        hashes = {
            name: sha256(function_body(source, signature).encode("utf-8"))
            for name, source in decoded.items()
        }
        if any(value != expected for value in hashes.values()):
            print(f"{label}: parser-body mismatch: {hashes}", file=sys.stderr)
            return 1

    cm_signature, cm_historical_hash = FUNCTIONS["CM31::from_le_bytes"]
    historical_sources = ("pinned_current", "R492", "R567")
    cm_historical = {
        name: sha256(function_body(decoded[name], cm_signature).encode("utf-8"))
        for name in historical_sources
    }
    if any(value != cm_historical_hash for value in cm_historical.values()):
        print(f"CM31 historical parser-body mismatch: {cm_historical}", file=sys.stderr)
        return 1
    cm_candidate_hash = sha256(function_body(decoded["candidate-archive"], cm_signature).encode("utf-8"))
    cm_working_hash = sha256(function_body(decoded["working-tree"], cm_signature).encode("utf-8"))
    if working_variant == "historical-baseline":
        if cm_working_hash != cm_historical_hash:
            print("baseline working-tree CM31 body differs from historical body", file=sys.stderr)
            return 1
        print(f"CM31 parser-body sha256 {cm_historical_hash}; historical body identical")
    else:
        if cm_candidate_hash == cm_historical_hash or cm_working_hash != cm_candidate_hash:
            print("candidate CM31 body is not the pinned isolated candidate body", file=sys.stderr)
            return 1
        print(
            f"CM31 candidate parser-body sha256 {cm_candidate_hash}; archived patch output matches; "
            "candidate body is not historically identical"
        )
    print("M31 and QM31 parser bodies match all three historical references in either variant")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
