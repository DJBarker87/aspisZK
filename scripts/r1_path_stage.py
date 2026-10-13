#!/usr/bin/env python3
"""Run one bounded 100-bit-path SBF/LiteSVM diagnostic stage on the NUC.

The script is intentionally an orchestrator only: it never synchronizes source,
generates fixtures, runs tests, or removes failed artifacts.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import socket
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
EXPECTED_CWD = Path("/home/dombarker/project-offloads/aspis-100bit-path-20261013")
EXPECTED_HOST = "nuc"
RESULTS = ROOT / "results/100bit-path-20261013"
OLD_FIXTURES = Path("/home/dombarker/project-offloads/aspis-r1-p2-20261010/results/r1-precheck-20261010/S2/fixtures")
CARGO_TARGET = Path("/home/dombarker/project-offloads/aspis-r1-p2-20261010/target")
SOLANA_BIN = Path(
    "/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin"
)
CARGO_BIN = Path("/home/dombarker/.cargo/bin")
RECORDER = ROOT / "scripts/v8_state_only_cu_record.py"
STACK_AUDIT = ROOT / "scripts/r1_p2_stack_audit.py"
BASELINE = "7742957648c33cf045eb6a672e7c7cc796b61087"
MEMORY_HIGH = "4G"
MEMORY_MAX = "6G"
MEMORY_MAX_BYTES = 6 * 2**30
SAFE_RESERVATION_BYTES = 50 * 2**30


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", help="lowercase stage label (letters, digits, hyphens)")
    parser.add_argument("--k", type=int, default=10)
    parser.add_argument("--fixture", choices=("transfer", "withdrawal"), default="transfer")
    parser.add_argument(
        "--fixture-source",
        type=Path,
        default=OLD_FIXTURES,
        help=f"directory containing proof/public/fixture metadata (default: {OLD_FIXTURES})",
    )
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z0-9-]+", args.stage):
        parser.error("stage must match [a-z0-9-]+")
    if not 0 <= args.k <= 22:
        parser.error("--k must be between 0 and 22")
    return args


def require_execution_location():
    hostname = socket.gethostname().split(".", 1)[0]
    if hostname != EXPECTED_HOST:
        raise RuntimeError(f"refusing to run outside {EXPECTED_HOST}: hostname={hostname!r}")
    cwd = Path.cwd().resolve()
    if cwd != EXPECTED_CWD:
        raise RuntimeError(f"refusing to run outside {EXPECTED_CWD}: cwd={cwd}")
    if ROOT.resolve() != EXPECTED_CWD:
        raise RuntimeError(f"script checkout is not the required source tree: {ROOT.resolve()}")


def source_files():
    selected = set()

    def add_matching(directory, predicate):
        if not directory.exists():
            return
        for path in directory.rglob("*"):
            if path.is_file() and predicate(path):
                selected.add(path)

    for path in ROOT.glob("Cargo*"):
        if path.is_file():
            selected.add(path)
    for directory in (ROOT / "crates", ROOT / "programs/r1-cost-probe", ROOT / "tools/r1-cost-probe"):
        add_matching(directory, lambda p: p.suffix == ".rs" or p.name in {"Cargo.toml", "build.rs"})
    for relative in (
        "scripts/r1_path_stage.py",
        "scripts/r1_p2_stack_audit.py",
        "scripts/v8_state_only_cu_record.py",
    ):
        path = ROOT / relative
        if path.is_file():
            selected.add(path)
    for pattern in ("rust-toolchain", "rust-toolchain.toml"):
        path = ROOT / pattern
        if path.is_file():
            selected.add(path)
    if not selected:
        raise RuntimeError("source selection is empty")
    return sorted(selected, key=lambda path: path.relative_to(ROOT).as_posix())


def freeze_manifest(stage, stage_dir):
    files = {
        path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in source_files()
    }
    encoded_files = json.dumps(files, sort_keys=True, separators=(",", ":")).encode()
    manifest_hash = hashlib.sha256(encoded_files).hexdigest()
    source_revision = f"{BASELINE}+{stage}+{manifest_hash}"
    manifest = {
        "schema": "aspis.100bit-path.actual-source-sha256.v1",
        "selection": "actual filesystem: root Cargo*, crates Rust/Cargo/build sources, R1 program and driver sources, stage/audit/receipt scripts",
        "source_revision": source_revision,
        "manifest_sha256": manifest_hash,
        "files": files,
    }
    path = stage_dir / "source-manifest.json"
    with path.open("x") as output:
        output.write(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    return manifest, source_revision


def active_reservations(stage, label):
    units = subprocess.check_output(
        ["systemctl", "--user", "list-units", "--type=scope", "--state=running", "--no-legend", "--plain"],
        text=True,
    )
    reservations = []
    for line in units.splitlines():
        fields = line.split()
        if not fields or fields[0] == "init.scope":
            continue
        values_text = subprocess.check_output(
            ["systemctl", "--user", "show", fields[0], "-p", "MemoryMax", "-p", "MemoryCurrent"],
            text=True,
        )
        values = dict(item.split("=", 1) for item in values_text.splitlines() if "=" in item)
        maximum = values.get("MemoryMax", "infinity")
        current = values.get("MemoryCurrent", "0")
        if maximum in {"infinity", "[not set]"}:
            raise RuntimeError(f"uncapped active scope {fields[0]}: {values}")
        if current in {"[not set]", "infinity"}:
            continue
        reservations.append({"unit": fields[0], "MemoryMax": maximum, "MemoryCurrent": current})
    reserved = sum(int(item["MemoryMax"]) for item in reservations)
    record = {
        "stage": stage,
        "label": label,
        "active_scopes": reservations,
        "new_memory_max_bytes": MEMORY_MAX_BYTES,
        "safe_working_limit_bytes": SAFE_RESERVATION_BYTES,
        "meminfo": Path("/proc/meminfo").read_text(),
    }
    out = RESULTS / f"{stage}-{label}-reservations.json"
    with out.open("x") as output:
        output.write(json.dumps(record, indent=2) + "\n")
    if reserved + MEMORY_MAX_BYTES > SAFE_RESERVATION_BYTES:
        raise RuntimeError(f"active MemoryMax reservations exceed safe limit: {reservations}")


def command_environment(source_revision):
    path = os.pathsep.join((str(CARGO_BIN), str(SOLANA_BIN), os.environ.get("PATH", "")))
    return {
        "PATH": path,
        "CARGO_TARGET_DIR": str(CARGO_TARGET),
        "CARGO_BUILD_JOBS": "2",
        "ASPIS_SOURCE_REVISION": source_revision,
    }


def run_scoped(stage, label, stem, command, env):
    active_reservations(stage, label)
    unit_digest = hashlib.sha256(f"{stage}:{label}".encode()).hexdigest()[:8]
    unit = f"aspis-1bp-{stage[:20]}-{label[:12]}-{unit_digest}"
    scoped = [
        "systemd-run",
        "--user",
        "--scope",
        f"--unit={unit}",
        "-p",
        f"MemoryHigh={MEMORY_HIGH}",
        "-p",
        f"MemoryMax={MEMORY_MAX}",
        "-p",
        "MemorySwapMax=0",
        "-p",
        "TasksMax=128",
        "env",
    ]
    scoped.extend(f"{key}={value}" for key, value in env.items())
    scoped.extend(("python3", str(RECORDER), str(stem), *map(str, command)))
    print(f"[{label}] scoped command: {' '.join(map(str, command))}", flush=True)
    subprocess.run(scoped, cwd=ROOT, check=True)


def copy_fixture_files(stage_dir, fixture, source=OLD_FIXTURES):
    source = Path(source)
    destination = stage_dir / "S2/fixtures"
    destination.mkdir(parents=True, exist_ok=False)
    names = (
        f"{fixture}.proof.bin",
        f"{fixture}.public.bin",
        f"{fixture}.fixture.json",
    )
    input_hashes = {}
    for name in names:
        source_path = source / name
        if not source_path.is_file():
            raise FileNotFoundError(f"missing fixture input: {source_path}")
        target_path = destination / name
        content = source_path.read_bytes()
        with target_path.open("xb") as output_file:
            output_file.write(content)
        input_hashes[name] = hashlib.sha256(content).hexdigest()
    provenance = {
        "schema": "aspis.r1-path.fixture-inputs.v1",
        "fixture": fixture,
        "source_directory": str(source.resolve()),
        "files": input_hashes,
    }
    provenance_path = destination / "fixture-source.json"
    with provenance_path.open("x") as output:
        output.write(json.dumps(provenance, indent=2, sort_keys=True) + "\n")
    return destination


def main():
    args = parse_args()
    require_execution_location()
    RESULTS.mkdir(parents=True, exist_ok=True)
    stage_dir = RESULTS / args.stage
    sbf_receipt = RESULTS / f"{args.stage}-sbf.json"
    if sbf_receipt.exists():
        raise RuntimeError(f"refusing unchanged stage rerun; receipt exists: {sbf_receipt}")
    if stage_dir.exists():
        raise RuntimeError(f"refusing to overwrite existing stage artifacts: {stage_dir}")
    stage_dir.mkdir()
    manifest, source_revision = freeze_manifest(args.stage, stage_dir)
    env = command_environment(source_revision)

    bin_dir = stage_dir / "bin"
    bin_dir.mkdir()
    sbf_command = [
        "cargo",
        "build-sbf",
        "--manifest-path",
        "programs/r1-cost-probe/Cargo.toml",
        "--sbf-out-dir",
        str(bin_dir),
        "--",
        "--locked",
        "-j",
        "2",
    ]
    run_scoped(args.stage, "sbf", RESULTS / f"{args.stage}-sbf", sbf_command, env)

    stripped_elf = bin_dir / "aspis_r1_cost_probe_program.so"
    unstripped_source = CARGO_TARGET / "sbpf-solana-solana/release/aspis_r1_cost_probe_program.so"
    unstripped_elf = bin_dir / "aspis_r1_cost_probe_program.unstripped.so"
    if not stripped_elf.is_file():
        raise FileNotFoundError(f"SBF build did not produce {stripped_elf}")
    if not unstripped_source.is_file():
        raise FileNotFoundError(f"SBF build did not produce unstripped ELF {unstripped_source}")
    with unstripped_source.open("rb") as source, unstripped_elf.open("xb") as target:
        shutil.copyfileobj(source, target)

    stack_dir = stage_dir / "stack"
    run_scoped(
        args.stage,
        "stack",
        RESULTS / f"{args.stage}-stack",
        ["python3", str(STACK_AUDIT), str(RESULTS / f"{args.stage}-sbf.log"), str(unstripped_elf), str(stripped_elf), str(stack_dir)],
        env,
    )
    stack_record = json.loads((stack_dir / "stack-audit.json").read_text())
    if stack_record["reachable_diagnostics"] or not stack_record["all_diagnostic_functions_absent_from_linked_elf"]:
        raise RuntimeError("stack audit did not pass; stopping before diagnostic")

    fixture_dir = copy_fixture_files(stage_dir, args.fixture, args.fixture_source)
    driver = CARGO_TARGET / "release/aspis-r1-cu-probe"
    if not driver.is_file():
        raise FileNotFoundError(f"release CU driver missing: {driver}")
    (stage_dir / "driver-sha256.txt").write_text(hashlib.sha256(driver.read_bytes()).hexdigest()+"\n")
    run_scoped(
        args.stage,
        "diagnostic",
        RESULTS / f"{args.stage}-diagnostic",
        [str(driver), "diagnostic", str(stripped_elf), str(stage_dir / "S2"), args.fixture, str(args.k)],
        env,
    )

    measurement_dir = stage_dir / "S2/measurements"
    for transaction in (1, 2):
        result_path = measurement_dir / f"{args.fixture}-diagnostic-k{args.k}-tx{transaction}-run1.json"
        result = json.loads(result_path.read_text())
        print(
            f"{args.fixture} diagnostic k={args.k} tx{transaction}: "
            f"verifier_cu={result['verifier_cu']}, "
            f"verifier_completed={result['verifier_completed']}, "
            f"heap={result['sbf_heap_high_water_bytes']}",
            flush=True,
        )
    print(
        f"stage={args.stage} source_revision={source_revision} "
        f"manifest_files={len(manifest['files'])} artifacts={stage_dir}",
        flush=True,
    )


if __name__ == "__main__":
    main()
