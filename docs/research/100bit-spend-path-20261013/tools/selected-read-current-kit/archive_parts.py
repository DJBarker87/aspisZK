"""Validate and reassemble accepted evidence in a temporary file outside Git."""
from contextlib import contextmanager
from pathlib import Path
import hashlib
import json
import tempfile


def _local_file(directory, name):
    assert isinstance(name, str) and Path(name).name == name and name not in {"", ".", ".."}
    path = directory / name
    assert not path.is_symlink() and path.is_file(), path
    return path


@contextmanager
def accepted_archive(evidence, packet):
    evidence = Path(evidence).resolve()
    manifest = json.loads((evidence / "reassembly-manifest.json").read_text())
    assert manifest["format"] == 1
    for key in ("archive", "archive_bytes", "archive_sha256"):
        assert manifest[key] == packet[key], key
    assert manifest["maximum_part_bytes"] == 80_000_000
    assert len(manifest["parts"]) == 2
    member_pin = manifest["member_manifest"]
    member_path = _local_file(evidence, member_pin["file"])
    assert member_path.stat().st_size == member_pin["bytes"]
    with member_path.open("rb") as source:
        assert hashlib.file_digest(source, "sha256").hexdigest() == member_pin["sha256"]
    members = json.loads(member_path.read_text())
    assert members["format"] == 1
    for key in ("archive", "archive_bytes", "archive_sha256"):
        assert members[key] == packet[key], key
    assert len(members["members"]) == packet["members"]

    repository = next(parent for parent in evidence.parents if (parent / ".git").exists())
    temporary_directory = Path(tempfile.gettempdir()).resolve()
    if temporary_directory.is_relative_to(repository):
        temporary_directory = Path("/tmp").resolve()
    assert not temporary_directory.is_relative_to(repository)
    combined = hashlib.sha256()
    total = 0
    names = set()
    # Unlinked on Unix and removed on exit everywhere; never reconstruct in Git.
    with tempfile.TemporaryFile(prefix="selected-read-evidence-", dir=temporary_directory) as archive:
        for pin in manifest["parts"]:
            assert pin["file"] not in names
            names.add(pin["file"])
            assert pin["offset"] == total
            assert 0 < pin["bytes"] <= manifest["maximum_part_bytes"]
            part = _local_file(evidence, pin["file"])
            assert part.stat().st_size == pin["bytes"], part
            part_hash = hashlib.sha256()
            part_bytes = 0
            with part.open("rb") as source:
                while block := source.read(1_048_576):
                    archive.write(block)
                    part_hash.update(block)
                    combined.update(block)
                    part_bytes += len(block)
            assert part_bytes == pin["bytes"]
            assert part_hash.hexdigest() == pin["sha256"], part
            total += part_bytes
        assert total == packet["archive_bytes"]
        assert combined.hexdigest() == packet["archive_sha256"]
        archive.flush()
        archive.seek(0)
        yield archive, members["members"]
