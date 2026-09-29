#!/usr/bin/env python3
"""Reject a retired public wallet identifier without embedding its literal value."""
import hashlib
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN_SHA256 = "c3c9cbc99fe0bcc3e664a2a8a03823bdd9fe0bcf6744912d494270d93b164aa1"
CANDIDATE = re.compile(rb"(?=([1-9A-HJ-NP-Za-km-z]{44}))")


def contains_forbidden(data, fingerprint=FORBIDDEN_SHA256):
    return any(hashlib.sha256(match[1]).hexdigest() == fingerprint
               for match in CANDIDATE.finditer(data))


def check_stream(stream):
    tail = b""
    while chunk := stream.read(1024 * 1024):
        data = tail + chunk
        if contains_forbidden(data):
            return True
        tail = data[-43:]
    return False


def main():
    if "--self-test" in sys.argv:
        artificial = b"2" * 44
        fingerprint = hashlib.sha256(artificial).hexdigest()
        assert contains_forbidden(b"x" + artificial + b"y", fingerprint)
        assert not contains_forbidden(b"2" * 43, fingerprint)
        assert not contains_forbidden(b"3" * 44, fingerprint)
    paths = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT).split(b"\0")
    failures = []
    for raw in paths:
        if not raw:
            continue
        path = ROOT / raw.decode("utf-8", errors="surrogateescape")
        if path.is_symlink():
            found = contains_forbidden(__import__("os").readlink(path).encode())
        elif path.is_file():
            with path.open("rb") as stream:
                found = check_stream(stream)
        else:
            continue  # Deleted working-tree files cannot publish the identifier.
        if found:
            failures.append(str(path.relative_to(ROOT)))
    if failures:
        print("FAIL: retired wallet identifier in tracked content:", file=sys.stderr)
        print("\n".join(failures), file=sys.stderr)
        return 1
    print("PASS: tracked content contains no retired wallet identifier")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
