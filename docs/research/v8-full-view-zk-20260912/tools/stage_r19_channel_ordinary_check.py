#!/usr/bin/env python3
"""Stage a fresh, source-only R19 channel ordinary differential checker."""
import argparse
import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXPERIMENTS = Path("docs/research/v8-no-work-100-20260907/experiments")
BIN_MANIFEST = Path("docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml")
EXCLUDED = {"sbf-primary", "host-c", "wire-controls-c", "logs", "keypair"}
IMAGE_BODY_SHA256 = "00d90aa42db587167c3288c533b3040c09f4514811a3fd299c0d7dc30b1162d4"

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")

def ignore_generated(_directory: str, names: list[str]) -> set[str]:
    return {name for name in names if name in EXCLUDED or
            name.startswith(("sbf-primary", "host-c", "wire-controls-c"))}

def image_body_sha(path: Path) -> str:
    text = path.read_text()
    start = text.index("fn image_terminal(")
    end = text.index("\n}\n", start) + 2
    return hashlib.sha256(text[start:end].encode()).hexdigest()

def validate_stage(stage: Path) -> dict:
    manifest_path = stage / "r18-stage.json"
    if not manifest_path.is_file():
        fail(f"R18 stage manifest missing: {manifest_path}")
    meta = json.loads(manifest_path.read_text())
    for name, expected in meta["files"].items():
        path = stage / name
        if not path.is_file():
            fail(f"R18 manifest file missing: {name}")
        actual = sha(path)
        if actual != expected:
            fail(f"R18 hash mismatch: {name}: {actual} != {expected}")
    return meta

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    stage, output = args.stage.resolve(), args.output.resolve()
    if not stage.is_dir(): fail(f"stage directory missing: {stage}")
    if output.exists(): fail(f"output already exists: {output}")
    r18 = validate_stage(stage)
    source_callback = stage / EXPERIMENTS / "relation_callback.rs"
    if image_body_sha(source_callback) != IMAGE_BODY_SHA256:
        fail("relation_callback image_terminal body hash drift")
    shutil.copytree(stage, output, ignore=ignore_generated)
    root = output / EXPERIMENTS
    checker = root / "r19_channel_ordinary_check.rs"
    shutil.copy2(HERE / "r19_channel_ordinary_check.rs", checker)
    cargo = output / BIN_MANIFEST
    cargo_text = cargo.read_text()
    name = 'name="r19-channel-ordinary-check"'
    if name in cargo_text: fail("checker binary already present")
    cargo.write_text(cargo_text + '\n[[bin]]\nname="r19-channel-ordinary-check"\npath="../r19_channel_ordinary_check.rs"\n')
    r18["files"][str(BIN_MANIFEST)] = sha(cargo)
    r18["files"][str(EXPERIMENTS / checker.name)] = sha(checker)
    r18["channel_ordinary_checker"] = {
        "checker_sha256": sha(checker),
        "cargo_sha256": sha(cargo),
        "image_terminal_source_sha256": IMAGE_BODY_SHA256,
    }
    (output / "r18-stage.json").write_text(json.dumps(r18, indent=2) + "\n")
    provenance = {
        "experiment": "R19 channel ordinary source differential; no SBF build",
        "predecessor": str(stage),
        "r18_manifest_sha256": sha(stage / "r18-stage.json"),
        "r18_profile": r18.get("profile"),
        "checker_sha256": sha(checker),
        "image_terminal_source_sha256": IMAGE_BODY_SHA256,
        "checker": "ordinary + beta*kappa*compact-G vs dense ordinary/G lerp; mixed image weights",
        "source_only": True, "crypto_or_soundness_claim": False,
    }
    (output / "r19-channel-ordinary-check-stage.json").write_text(json.dumps(provenance, indent=2) + "\n")
    print(json.dumps({"stage": str(output), "checker": str(checker), "cargo_bin": "r19-channel-ordinary-check"}))

if __name__ == "__main__":
    main()
