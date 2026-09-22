#!/usr/bin/env python3
"""Install the R19 factored T163 ordinary-terminal experiment.

This is deliberately a source-local adapter.  It refuses to guess a stage,
validates the packet and its literal 1024-entry ORDER, and returns the paths it
changed.  It does not build, run, or alter the frozen input tree.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import shutil
from pathlib import Path

EXPERIMENTS = Path("docs/research/v8-no-work-100-20260907/experiments")
REQUIRED_PACKET = ("src/factored_correction.rs", "src/correction_tables.rs")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _function(text: str, marker: str) -> tuple[int, int, str]:
    """Return [start,end) for one Rust function, using balanced braces."""
    start = text.find(marker)
    if start < 0:
        raise ValueError(f"missing function marker: {marker}")
    brace = text.find("{", start)
    if brace < 0:
        raise ValueError(f"missing function body: {marker}")
    depth = 0
    for i in range(brace, len(text)):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                return start, i + 1, text[start : i + 1]
    raise ValueError(f"unbalanced function body: {marker}")


def _replace_function(text: str, marker: str, replacement: str) -> str:
    start, end, _ = _function(text, marker)
    return text[:start] + replacement + text[end:]


def _validate_packet(packet: Path) -> None:
    manifest = json.loads((packet / "MANIFEST.json").read_text())
    for name, info in manifest["files"].items():
        path = packet / name
        if not path.is_file() or path.stat().st_size != info["bytes"] or sha256(path) != info["sha256"]:
            raise ValueError(f"packet manifest mismatch: {name}")
    for name in REQUIRED_PACKET:
        if not (packet / name).is_file():
            raise ValueError(f"packet file missing: {name}")


def _validate_order(root: Path, packet: Path) -> None:
    plan = json.loads((packet / "evidence/correction_plan.json").read_text())
    expected = plan.get("order")
    if not isinstance(expected, list) or len(expected) != 1024:
        raise ValueError("packet correction plan has no 1024-entry order")
    basis = root / EXPERIMENTS / "r17_basis_tables.rs"
    if not basis.is_file():
        raise ValueError("stage has no retained basis ORDER source")
    match = re.search(r"\bORDER\s*:\s*\[usize\s*;\s*1024\s*\]\s*=\s*(\[[\s\S]*?\])\s*;", basis.read_text())
    if not match or ast.literal_eval(match.group(1)) != expected:
        raise ValueError(f"staged ORDER differs from packet plan: {basis}")


def _new_one_terminal(old: str) -> str:
    head = old[: old.find("{")]
    if "->[K;4]" not in head.replace(" ", ""):
        raise ValueError("one_terminal must retain an explicit [K;4] return type")
    return head + r'''{
    assert!(off==0 && add_pivot);
    let (normal,carry,high)=kernel.geometry_parts();
    let first=factored_correction::evaluate(
        factors[0..16].try_into().unwrap(),
        factors[16..80].try_into().unwrap(),
        normal,carry,high,delta);
    let second=factored_correction::evaluate(
        factors[80..96].try_into().unwrap(),
        factors[96..160].try_into().unwrap(),
        normal,carry,high,delta);
    let d:[K;4]=core::array::from_fn(|i|first[i].add(second[i]));
    let wp=entry(factors,off,1023);
    core::array::from_fn(|i|plain[i].add(d[i]).sub(wp.mul(inactive[i]))
        .add(if add_pivot {pivot[i]} else {K::ZERO}))
}'''


def _modernize_terminal(fn_text: str) -> str:
    fn_text = fn_text.replace(
        "let (delta,rest)=workspace.split_at_mut(163);",
        "let (factors,rest)=workspace.split_at_mut(240);",
    )
    fn_text = fn_text.replace(
        "let (factors,sums)=rest.split_at_mut(240);",
        "let (scratch,sums)=rest.split_at_mut(240);",
    )
    fn_text = fn_text.replace(
        "one_terminal(factors,0,plain_a,delta,",
        "one_terminal(factors,0,plain_a,scratch,",
    )
    if "split_at_mut(240)" not in fn_text or "plain_a,scratch" not in fn_text:
        raise ValueError("terminal workspace/call shape did not match R19 source")
    return fn_text


def _add_factored_module(text: str) -> str:
    """Add the sibling module without capturing an existing path attribute."""
    if "mod r19_factored_correction;" in text:
        return text
    path_decl = '#[path="r19_channel_ordinary.rs"]\n'
    if path_decl in text:
        return text.replace(
            path_decl,
            '#[path="r19_factored_correction.rs"] mod r19_factored_correction;\n' + path_decl,
            1,
        )
    marker = "mod r19_channel_ordinary;"
    if text.count(marker) != 1:
        raise ValueError("ordinary module declaration drifted")
    return text.replace(marker, "mod r19_factored_correction;\n" + marker, 1)


def apply(root: str | Path, packet: str | Path | None = None) -> list[Path]:
    root = Path(root).resolve()
    packet_path = Path(packet).resolve() if packet else Path(__file__).resolve().parents[1] / "r19-pack"
    source = root / EXPERIMENTS / "r19_channel_ordinary.rs"
    if not source.is_file():
        raise FileNotFoundError(source)
    if "factored_correction::evaluate" in source.read_text():
        raise ValueError("R19 factored adapter already applied")
    _validate_packet(packet_path)
    _validate_order(root, packet_path)

    text = source.read_text()
    if not re.search(r"fn\s+geometry_parts\s*\(", (root / EXPERIMENTS / "r17_weighted_groups.rs").read_text()):
        raise ValueError("shared geometry accessor is required before this adapter")

    _, _, old_one = _function(text, "fn one_terminal(")
    _, _, old_terminal = _function(text, "pub(super) fn terminal(")
    text = _replace_function(text, "fn one_terminal(", _new_one_terminal(old_one))
    text = _replace_function(text, "pub(super) fn terminal(", _modernize_terminal(old_terminal))
    if "pub(super) fn terminal_shared(" in text:
        text = _replace_function(text, "pub(super) fn terminal_shared(", _modernize_terminal(_function(text, "pub(super) fn terminal_shared(")[2]))
    # The old functions are retained for the independent source differential.
    reference_one = old_one.replace("fn one_terminal(", "fn one_terminal_reference(", 1)
    reference_terminal = old_terminal.replace("pub(super) fn terminal(", "pub(super) fn terminal_reference(", 1)
    reference_terminal = reference_terminal.replace("one_terminal(", "one_terminal_reference(")
    anchor = text.find("fn one_terminal(")
    if anchor < 0:
        raise ValueError("new one_terminal was not installed")
    text = text[:anchor] + reference_one + "\n\n" + text[anchor:]
    terminal_anchor = text.find("pub(super) fn terminal(")
    if terminal_anchor < 0:
        raise ValueError("new terminal was not installed")
    text = text[:terminal_anchor] + reference_terminal + "\n\n" + text[terminal_anchor:]
    if "use super::r19_factored_correction as factored_correction;" not in text:
        text = text.replace("use super::{corelib, basis_transport, r17_weighted_groups};", "use super::{corelib, basis_transport, r17_weighted_groups};\nuse super::r19_factored_correction as factored_correction;", 1)
    source.write_text(text)

    changed = [source]
    callback = root / EXPERIMENTS / "relation_callback.rs"
    if not callback.is_file():
        raise FileNotFoundError(callback)
    callback_text = callback.read_text()
    if "mod r19_factored_correction;" not in callback_text:
        callback.write_text(_add_factored_module(callback_text))
        changed.append(callback)
    for rel in REQUIRED_PACKET:
        destination = root / EXPERIMENTS / ("r19_factored_correction.rs" if rel.endswith("factored_correction.rs") else "correction_tables.rs")
        shutil.copy2(packet_path / rel, destination)
        if sha256(destination) != sha256(packet_path / rel):
            raise ValueError(f"copied packet file changed: {destination}")
        changed.append(destination)

    checker = root / EXPERIMENTS / "r19_channel_ordinary_check.rs"
    if not checker.is_file():
        shutil.copy2(Path(__file__).with_name("r19_channel_ordinary_check.rs"), checker)
        if checker not in changed:
            changed.append(checker)
    if "terminal_reference" not in checker.read_text():
        c = checker.read_text()
        if "mod r19_factored_correction;" not in c:
            c = _add_factored_module(c)
        needle = "        assert_eq!(candidate, dense, \"ordinary/G dense lerp case {case}\");"
        addition = needle + "\n        let mut reference_workspace = vec![K::ZERO; 1024];\n        let reference = r19_channel_ordinary::terminal_reference(&audit, abc, alpha, beta, &mut reference_workspace);\n        assert_eq!(reference, ordinary, \"retained ordinary R19 reference case {case}\");\n        let kernel=r17_weighted_groups::Kernel::new(abc,alpha);\n        let shared=r19_channel_ordinary::terminal_shared(&audit,abc,alpha,beta,&mut reference_workspace,&kernel);\n        assert_eq!(shared,ordinary,\"shared ordinary case {case}\");"
        if c.count(needle) != 1:
            raise ValueError("ordinary differential assertion drifted")
        checker.write_text(c.replace(needle, addition, 1))
        if checker not in changed:
            changed.append(checker)
    return changed


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--packet", type=Path)
    args = parser.parse_args()
    print(json.dumps({"changed": [str(p) for p in apply(args.root, args.packet)]}))


if __name__ == "__main__":
    main()
