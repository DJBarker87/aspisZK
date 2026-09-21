#!/usr/bin/env python3
"""Stage the optional R19 factored T163 correction on a retained R18 tree.

This adapter is deliberately source-only.  It copies a validated R18 stage,
checks the packet's signed-map inventory against the actual staged ORDER, and
installs the one-terminal adapter used by both the primary and the existing
host differential checker.  No build or runtime gate is run here.
"""
import argparse
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent
PACKET = RESEARCH / "r19-pack"
EXPERIMENTS = Path("docs/research/v8-no-work-100-20260907/experiments")
EXCLUDED_GENERATED = {"evidence", "audit", "outputs", "target", "keys"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def ignore_generated(_directory: str, names: list[str]) -> set[str]:
    """Keep source and opening-gate.log, but never copy generated/key material."""
    ignored = set()
    for name in names:
        lower = name.lower()
        if name == "opening-gate.log":
            continue
        if lower in EXCLUDED_GENERATED or lower.startswith(("sbf", "host", "wire-controls")):
            ignored.add(name)
    return ignored


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        fail(f"{label}: expected one match, found {count}")
    return text.replace(old, new, 1)


def validate_packet() -> dict:
    manifest_path = PACKET / "MANIFEST.json"
    if not manifest_path.is_file():
        fail(f"packet manifest missing: {manifest_path}")
    manifest = json.loads(manifest_path.read_text())
    for name, entry in manifest["files"].items():
        path = PACKET / name
        if not path.is_file():
            fail(f"packet file missing: {name}")
        if path.stat().st_size != entry["bytes"] or sha(path) != entry["sha256"]:
            fail(f"packet hash/size mismatch: {name}")
    required = [
        PACKET / "src/factored_correction.rs",
        PACKET / "src/correction_tables.rs",
        PACKET / "tools/check_stage_inventory.py",
    ]
    for path in required:
        if not path.is_file():
            fail(f"required packet artifact missing: {path}")
    return manifest


def validate_r18(stage: Path) -> dict:
    manifest_path = stage / "r18-stage.json"
    if not manifest_path.is_file():
        fail(f"R18 stage manifest missing: {manifest_path}")
    meta = json.loads(manifest_path.read_text())
    if not meta.get("compact_primary") or meta.get("current_T_unchanged"):
        fail("input is not the retained compact R18 minimum-T stage")
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
    parser.add_argument("--stage", type=Path, required=True,
                        help="validated R18 stage directory")
    parser.add_argument("--output", type=Path, required=True,
                        help="fresh output directory (must not exist)")
    args = parser.parse_args()
    stage = args.stage.resolve()
    output = args.output.resolve()
    if output.exists():
        fail(f"output already exists: {output}")
    if not stage.is_dir():
        fail(f"stage directory missing: {stage}")

    packet_manifest = validate_packet()
    r18 = validate_r18(stage)
    basis = stage / EXPERIMENTS / "r17_basis_tables.rs"
    if not basis.is_file():
        fail(f"staged basis table missing: {basis}")
    inventory = subprocess.run(
        ["python3", str(PACKET / "tools/check_stage_inventory.py"), str(basis)],
        cwd=PACKET, check=False, capture_output=True, text=True,
    )
    if inventory.returncode != 0:
        fail("packet stage-inventory gate failed:\n" + inventory.stdout + inventory.stderr)

    shutil.copytree(stage, output, ignore=ignore_generated)
    # A clone exclusion must never silently discard a source pin.
    for name in r18["files"]:
        if not (output / name).is_file():
            fail(f"clone exclusion removed a pinned input: {name}")
    root = output / EXPERIMENTS
    changes = {}

    def edit(name: str, transform) -> None:
        path = root / name
        before = sha(path)
        updated = transform(path.read_text())
        if updated == path.read_text():
            fail(f"no change made to {name}")
        path.write_text(updated)
        changes[str(EXPERIMENTS / name)] = {
            "before_sha256": before,
            "after_sha256": sha(path),
        }

    # Install packet sources beside the retained experiments.  The table file
    # is included by factored_correction.rs, keeping the generated plan fixed.
    for name in ("factored_correction.rs", "correction_tables.rs"):
        # The candidate includes correction_tables.rs by its literal sibling
        # name; retain that name in the staged experiment directory.
        target = root / ("r19_factored_correction.rs" if name == "factored_correction.rs" else name)
        shutil.copy2(PACKET / "src" / name, target)
        changes[str(EXPERIMENTS / target.name)] = {
            "before_sha256": None,
            "after_sha256": sha(target),
            "packet_sha256": sha(PACKET / "src" / name),
        }

    # The checker is the existing R18 dense oracle; only add the candidate
    # module so the same arbitrary-input cases exercise the staged kernel.
    def checker(s: str) -> str:
        return replace_once(s, "mod r18_shared_ordinary;",
                            "#[path=\"r19_factored_correction.rs\"] mod r19_factored_correction;\nmod r18_shared_ordinary;",
                            "checker factored module")
    edit("r18_shared_ordinary_check.rs", checker)

    # The production-shaped relation callback has the same parent-module
    # topology as the checker.  Keep all old calls and dense references.
    def callback(s: str) -> str:
        return replace_once(s, "mod r18_shared_ordinary;",
                            "#[path=\"r19_factored_correction.rs\"] mod r19_factored_correction;\nmod r18_shared_ordinary;",
                            "relation factored module")
    edit("relation_callback.rs", callback)

    def kernel(s: str) -> str:
        return replace_once(
            s,
            "pub(super) struct Kernel { normal:[K;16],carry:[K;3],high:[K;16],prepared_carry:[PreparedQm31Multiplier;3] }",
            "pub(super) struct Kernel { pub(super) normal:[K;16],pub(super) carry:[K;3],pub(super) high:[K;16],prepared_carry:[PreparedQm31Multiplier;3] }",
            "factored kernel field contract")
    edit("r17_weighted_groups.rs", kernel)

    def ordinary(s: str) -> str:
        s = replace_once(s, 'include!("r17_reused_block_terminal.rs");',
                         'include!("r17_reused_block_terminal.rs");\nuse super::r19_factored_correction as factored;',
                         "factored ordinary import")
        start = s.index("fn one_terminal(")
        end = s.index("\n}\n\n/// Return exactly four", start) + 2
        # Keep this replacement intentionally explicit; it avoids a broad
        # regex over the sensitive terminal and makes omissions fail.
        # The candidate intentionally has no inactive helper.  Construct the
        # final expression from the retained grouped kernel contract instead.
        replacement = '''fn one_terminal(factors:&[K], off:usize, plain:[K;4],
    scratch:&mut[K], sums:&mut[K], kernel:&r17_weighted_groups::Kernel,
    inactive:[K;4], pivot:[K;4], add_pivot:bool)->[K;4] {
    assert!(factors.len() >= off + 80);
    let first = factored::evaluate(
        factors[off..off+16].try_into().unwrap(),
        factors[off+16..off+80].try_into().unwrap(),
        &kernel.normal, &kernel.carry, &kernel.high, scratch);
    let correction = if add_pivot {
        let second = factored::evaluate(
            factors[80..96].try_into().unwrap(),
            factors[96..160].try_into().unwrap(),
            &kernel.normal, &kernel.carry, &kernel.high, scratch);
        core::array::from_fn(|i| first[i].add(second[i]))
    } else { first };
    let wp=entry(factors,off,1023);
    core::array::from_fn(|i|plain[i].add(correction[i]).sub(wp.mul(inactive[i]))
        .add(if add_pivot {pivot[i]} else {K::ZERO}))
}'''
        s = s[:start] + replacement + s[end:]
        s = replace_once(s, "    let (delta,rest)=workspace.split_at_mut(163);\n    let (factors,sums)=rest.split_at_mut(240);",
                         "    let (factors,rest)=workspace.split_at_mut(240);\n    let (scratch,sums)=rest.split_at_mut(240);",
                         "factored workspace layout")
        s = replace_once(s, "let a=one_terminal(factors,0,plain_a,delta,&mut sums[..128],&kernel,inactive,pivot,true);\n    let e=one_terminal(factors,160,plain_e,delta,&mut sums[..128],&kernel,inactive,pivot,false);",
                         "let a=one_terminal(factors,0,plain_a,scratch,&mut sums[..128],&kernel,inactive,pivot,true);\n    let e=one_terminal(factors,160,plain_e,scratch,&mut sums[..128],&kernel,inactive,pivot,false);",
                         "factored terminal calls")
        return s
    edit("r18_shared_ordinary.rs", ordinary)

    profile = r18["profile"]
    r19 = dict(r18)
    r19.update({
        "profile": profile,
        "experiment": "R19 factored T163 correction; source profile unchanged",
        "predecessor": str(stage),
        "r18_manifest_sha256": sha(stage / "r18-stage.json"),
        "packet_manifest_sha256": sha(PACKET / "MANIFEST.json"),
        "packet_base_commit": packet_manifest["base_commit"],
        "factored_scope": "one_terminal only; A offsets 0+80, E offset 160",
        "retained": ["plain terminal", "inactive subtraction", "pivot", "all 64 groups", "1024 workspace"],
        "allocations": "caller-owned workspace; no new giant stack array",
        "source_gates_passed": False, "sbf_measured": False,
        "changes": changes,
    })
    r19["r18_files"] = dict(r18["files"])
    r19["files"] = {
        str(path.relative_to(output)): sha(path)
        for path in sorted(output.rglob("*")) if path.is_file()
        and path.name not in {"r18-stage.json", "r19-stage.json"}
    }
    (output / "r19-stage.json").write_text(json.dumps(r19, indent=2) + "\n")
    r18["r19_factored_changes"] = changes
    r18["r19_stage_sha256"] = sha(output / "r19-stage.json")
    r18["files"].update({name: value["after_sha256"] for name, value in changes.items()})
    (output / "r18-stage.json").write_text(json.dumps(r18, indent=2) + "\n")
    print(json.dumps({"stage": str(output), "profile": profile,
                      "inventory": inventory.stdout.strip(),
                      "r19_manifest": str(output / "r19-stage.json")}))


if __name__ == "__main__":
    main()
