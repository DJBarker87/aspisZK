#!/usr/bin/env python3
"""Static R364 generated-source inventory; never runs Lean or external tools.

Usage after the lead supplies a completed R364 result directory:
  python3 census_generated_sources.py --result-dir PATH [--llbc PATH] [--out PATH]

The census records declarations, imports, type attributes, and opaque/template
markers as observations only. It does not decide dependency closure or source
correspondence and must not be run on partial translation output.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any

EXPECTED_LLBC_SHA256 = "8b9bd55e374866294b591758e1282d08998cb002e30b070207156b61f81a69ca"
EXPECTED_FUNS = {37: "branch", 39: "from_output", 40: "from_residual"}
EXPECTED_TYPES = {14, 20, 21, 22}
MARKERS = {
    "axiom": r"\baxiom\b",
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "opaque": r"\bopaque\b",
    "unsafe": r"\bunsafe\b",
    "extern": r"\bextern\b",
    "implemented_by": r"\bimplemented_by\b",
    "external_template": r"External_Template|external[_ ]template",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest_json(obj: Any) -> str:
    return sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode())


def resolve_hc(value: Any, table: dict[int, Any]) -> Any:
    """Resolve Charon HashConsedValue/Deduplicated wrappers recursively."""
    if isinstance(value, dict):
        if "HashConsedValue" in value:
            wrapped = value["HashConsedValue"]
            if isinstance(wrapped, dict) and "id" in wrapped and "value" in wrapped:
                table[int(wrapped["id"])] = wrapped["value"]
                return resolve_hc(wrapped["value"], table)
            if isinstance(wrapped, list) and len(wrapped) == 2:
                table[int(wrapped[0])] = wrapped[1]
                return resolve_hc(wrapped[1], table)
            return resolve_hc(wrapped, table)
        if "Deduplicated" in value:
            ref = value["Deduplicated"]
            if isinstance(ref, dict):
                ref = ref.get("id", ref.get("value", ref))
            try:
                return resolve_hc(table[int(ref)], table)
            except (KeyError, TypeError, ValueError):
                return {"unresolved_deduplicated": ref}
        return {k: resolve_hc(v, table) for k, v in value.items()}
    if isinstance(value, list):
        return [resolve_hc(v, table) for v in value]
    return value


def collect_hc(value: Any, table: dict[int, Any]) -> None:
    """First pass: index every HashConsedValue before resolving any reference."""
    if isinstance(value, dict):
        wrapped = value.get("HashConsedValue")
        if isinstance(wrapped, dict) and "id" in wrapped and "value" in wrapped:
            table[int(wrapped["id"])] = wrapped["value"]
        elif isinstance(wrapped, list) and len(wrapped) == 2:
            table[int(wrapped[0])] = wrapped[1]
        for v in value.values():
            collect_hc(v, table)
    elif isinstance(value, list):
        for v in value:
            collect_hc(v, table)


def enum_payload(row: dict[str, Any], kind: str) -> dict[str, Any] | None:
    value = row.get(kind)
    if isinstance(value, dict):
        return value
    return None


def decl_id(payload: dict[str, Any] | None) -> int | None:
    if not payload:
        return None
    value = payload.get("id")
    if isinstance(value, dict):
        # LLBC ids are sometimes tagged, e.g. {"Fun": 40}.
        value = next(iter(value.values()), None)
    try:
        return int(value)
    except (TypeError, ValueError):
        return None


def read_llbc(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    if sha256(raw) != EXPECTED_LLBC_SHA256:
        raise SystemExit(f"LLBC SHA256 mismatch: {path} has {sha256(raw)}")
    obj = json.loads(raw)
    translated = obj.get("translated", {})
    table: dict[int, Any] = {}
    collect_hc(obj, table)
    decoded = resolve_hc(translated, table)
    errors = obj.get("has_errors")
    rows = decoded.get("ordered_decls", []) if isinstance(decoded, dict) else []
    fun_decls = decoded.get("fun_decls", []) if isinstance(decoded, dict) else []
    type_decls = decoded.get("type_decls", []) if isinstance(decoded, dict) else []
    fun_rows: dict[int, dict[str, Any]] = {
        int(f["def_id"]): f for f in fun_decls if isinstance(f, dict) and "def_id" in f
    }
    type_rows: dict[int, dict[str, Any]] = {
        int(t["def_id"]): t for t in type_decls if isinstance(t, dict) and "def_id" in t
    }
    ordered_ids: dict[str, list[int]] = {"Fun": [], "Type": []}
    for row in rows:
        if not isinstance(row, dict):
            continue
        for kind in ("Fun", "Type"):
            group = enum_payload(row, kind)
            if group is None:
                continue
            # Ordered declarations encode NonRec IDs or Rec groups.
            if "NonRec" in group:
                ordered_ids[kind].append(int(group["NonRec"]))
            elif "Rec" in group and isinstance(group["Rec"], list):
                ordered_ids[kind].extend(int(i) for i in group["Rec"])

    def source_name(item: dict[str, Any]) -> str | None:
        meta = item.get("item_meta", {})
        path_parts = meta.get("name", []) if isinstance(meta, dict) else []
        names = []
        for part in path_parts:
            if isinstance(part, dict) and "Ident" in part:
                ident = part["Ident"]
                if isinstance(ident, list) and ident:
                    names.append(str(ident[0]))
        return "::".join(names) if names else None

    names: dict[int, str | None] = {}
    for i, f in fun_rows.items():
        names[i] = source_name(f)
    type_names = {i: source_name(t) for i, t in type_rows.items()}
    return {
        "sha256": sha256(raw),
        "has_errors": errors,
        "ordered_decl_count": len(rows),
        "ordered_fun_ids": ordered_ids["Fun"],
        "ordered_type_ids": ordered_ids["Type"],
        "fun_ids_and_names": {str(i): names.get(i) for i in sorted(fun_rows)},
        "expected_root_funs_present": all(i in fun_rows for i in EXPECTED_FUNS),
        "expected_root_fun_name_matches": {
            str(i): names.get(i, "").split("::")[-1] == name for i, name in EXPECTED_FUNS.items()
        },
        "expected_root_type_names": {str(i): type_names.get(i) for i in sorted(EXPECTED_TYPES)},
        "expected_type_ids_present": EXPECTED_TYPES.issubset(type_rows),
        "resolved_hashcons_count": len(table),
    }


def lean_files(root: Path) -> list[dict[str, Any]]:
    files = sorted(root.rglob("*.lean"), key=lambda p: p.relative_to(root).as_posix())
    out: list[dict[str, Any]] = []
    for path in files:
        raw = path.read_bytes()
        text = raw.decode("utf-8", errors="replace")
        lines = text.splitlines()
        declarations = []
        for idx, line in enumerate(lines):
            line_no = idx + 1
            match = re.match(
                r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
                r"(def|theorem|lemma|axiom|opaque|abbrev|structure|inductive|class)\s*(.*)$",
                line,
            )
            if not match:
                continue
            kind, remainder = match.groups()
            name = remainder.split()[0] if remainder.split() else None
            if name is None and idx + 1 < len(lines):
                name = lines[idx + 1].strip().split()[0] if lines[idx + 1].strip() else None
            end = idx + 1
            while end < len(lines) and not (
                lines[end].startswith("/-- ") or lines[end].startswith("end ")
            ):
                end += 1
            declarations.append({
                "line": line_no,
                "kind": kind,
                "name": name,
                "span_end_line_exclusive": end + 1,
                "block_sha256": sha256("\n".join(lines[idx:end]).encode()),
                "source_lines": lines[idx:end],
            })
        imports = [
            {"line": i, "module": m.group(1)}
            for i, line in enumerate(text.splitlines(), 1)
            if (m := re.match(r"^\s*import\s+(.+?)\s*$", line))
        ]
        attributes = [
            {"line": i, "text": line.strip()}
            for i, line in enumerate(text.splitlines(), 1)
            if "rust_model" in line or "rust_type" in line or "rust_fun" in line
        ]
        marker_hits = {
            name: [
                {"line": i, "text": line.strip()[:240]}
                for i, line in enumerate(text.splitlines(), 1)
                if re.search(pattern, line, re.IGNORECASE)
            ]
            for name, pattern in MARKERS.items()
        }
        out.append({
            "path": path.relative_to(root).as_posix(),
            "bytes": len(raw),
            "sha256": sha256(raw),
            "imports": imports,
            "declarations": declarations,
            "rust_attributes": attributes,
            "marker_flags": marker_hits,
        })
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--result-dir", required=True, type=Path)
    parser.add_argument(
        "--llbc", type=Path,
        default=Path(".r21-scratch/r334-controlflow-source-projection/R334ControlFlowSourceProjection.llbc"),
    )
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if not args.result_dir.is_dir():
        raise SystemExit(f"result directory does not exist: {args.result_dir}")
    translation_path = args.result_dir / "translation.json"
    result_path = args.result_dir.parent / "result.json"
    translation = json.loads(translation_path.read_text()) if translation_path.is_file() else None
    result = json.loads(result_path.read_text()) if result_path.is_file() else None
    census = {
        "scope": "static generated-source census; observations only, no closure or semantics decision",
        "llbc": read_llbc(args.llbc),
        "generated_source_files": lean_files(args.result_dir),
        "translation_json": translation,
        "result_json": result,
        "result_json_status": "present" if result is not None else "not present; output completeness unknown",
        "partial_translation_warning": "No completeness is inferred from a directory scan; a failed translator result must remain diagnostic only.",
    }
    census["census_sha256"] = digest_json(census)
    rendered = json.dumps(census, indent=2) + "\n"
    if args.out:
        args.out.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
