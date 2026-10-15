#!/usr/bin/env python3
"""Check a pinned lexical call/loop audit, not a Rust CFG/refinement theorem.

Dependency-free, no compilation, no network. Repository inputs come only from
git blobs. Unknown source spans, invocations, loops and SDK/archive mismatches
fail closed. Explicit opaque boundaries remain OPEN, including in the default
summary. --require-closed-effects fails until those obligations are discharged.
The lexer is deliberately not advertised as a Rust parser or name resolver.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
DEFAULT_POLICY = HERE / "j1e-source-effect-policy.json"
FORM_WORDS = set("if while for match loop return let fn unsafe else move as in mut dyn impl".split())
CLASSES = {"expanded", "designated_hash", "pda_create", "constructor", "opaque"}
LOOP_CLASSES = {"fixed_range", "fixed_array", "state_rank", "opaque"}


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_bytes(revision: str, path: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(ROOT), "show", f"{revision}:{path}"])


def tokens(text: str) -> list[tuple[str, int, int]]:
    """Token spans; comments/literals cannot manufacture calls or braces."""
    out = []
    i = 0
    while i < len(text):
        start = i
        if text[i].isspace():
            i += 1
            continue
        if text.startswith("//", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            continue
        if text.startswith("/*", i):
            depth, i = 1, i + 2
            while depth and i < len(text):
                if text.startswith("/*", i): depth, i = depth + 1, i + 2
                elif text.startswith("*/", i): depth, i = depth - 1, i + 2
                else: i += 1
            if depth: raise ValueError("unterminated block comment")
            continue
        raw = re.match(r'(?:br|r)(#*)"', text[i:])
        if raw:
            end = text.find('"' + raw[1], i + len(raw[0]))
            if end < 0: raise ValueError("unterminated raw literal")
            i = end + 1 + len(raw[1])
            out.append(("LITERAL", start, i))
            continue
        literal = re.match(r"(?:b)?(?:\"(?:\\.|[^\"\\])*\"|'(?:\\.|[^'\\])')", text[i:], re.S)
        if literal:
            i += len(literal[0])
            out.append(("LITERAL", start, i))
            continue
        word = re.match(r"[A-Za-z_][A-Za-z_0-9]*|[0-9][A-Za-z_0-9]*|::|\.\.=|\.\.|->|=>|&&|\|\||[<>!=+*/%-]=", text[i:])
        if word: i += len(word[0])
        else: i += 1
        out.append((text[start:i], start, i))
    return out


def brackets(ts: list[tuple[str, int, int]]) -> dict[int, int]:
    stack, pairs = [], {}
    for i, (value, _, _) in enumerate(ts):
        if value in ("(", "[", "{"): stack.append((value, i))
        elif value in (")", "]", "}"):
            if not stack or {"(": ")", "[": "]", "{": "}"}[stack[-1][0]] != value:
                raise ValueError("unbalanced delimiters")
            _, left = stack.pop()
            pairs[left], pairs[i] = i, left
    if stack: raise ValueError("unclosed delimiter")
    return pairs


def fragment(raw: bytes, anchor: str) -> tuple[str, int, int, int, int]:
    text = raw.decode()
    at = text.find(anchor)
    if at < 0 or text.find(anchor, at + 1) >= 0:
        raise ValueError(f"anchor is absent/ambiguous: {anchor}")
    ts = tokens(text)
    pairs = brackets(ts)
    opening = next(i for i, t in enumerate(ts) if t[1] >= at and t[0] == "{")
    closing = pairs[opening]
    start = text.rfind("\n", 0, at) + 1
    end = ts[closing][2]
    return text[start:end], len(text[:start].encode()), len(text[:end].encode()), text.count("\n", 0, start) + 1, text.count("\n", 0, end) + 1


def invocation_name(ts, index, pairs):
    j = index - 1
    if j < 0: return None
    if ts[j][0] == "!":
        if j < 1 or ts[j - 1][0] in FORM_WORDS:
            return None  # e.g. `if !(...)`, not a macro invocation
        return "macro::" + ts[j - 1][0]
    if ts[j][0] in (")", "]"):
        left = pairs[j]
        return "callable::" + "".join(t[0] for t in ts[left:j + 1])
    if ts[j][0] == ">":
        depth = 1
        j -= 1
        while j >= 0 and depth:
            if ts[j][0] == ">": depth += 1
            elif ts[j][0] == "<": depth -= 1
            j -= 1
        if depth or j < 0 or ts[j][0] != "::": return None
        j -= 1
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", ts[j][0]): return None
    if ts[j][0] in FORM_WORDS or (j and ts[j - 1][0] == "fn"): return None
    if j and ts[j - 1][0] == ".": return "method::" + ts[j][0]
    start = j
    while start >= 2 and ts[start - 1][0] == "::" and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", ts[start - 2][0]):
        start -= 2
    return "".join(t[0] for t in ts[start:j + 1])


def inventory(text: str, first_line: int):
    """Lexical sites, including cfg alternatives; deliberately not a CFG.

    cfg attributes are recorded separately, not executed by this lexer. Thus an
    inactive alternative can never silently disappear from the audit. A later
    compiler/lowering bridge must instantiate the pinned feature configuration.
    """
    ts = tokens(text)
    pairs = brackets(ts)
    attrs, excluded = [], set()
    for i in range(len(ts) - 1):
        if ts[i][0] == "#" and ts[i + 1][0] == "[":
            end = pairs[i + 1]
            attrs.append(text[ts[i][1]:ts[end][2]])
            excluded.update(range(i, end + 1))
    body = next(i for i, t in enumerate(ts) if t[0] == "{")
    calls, loops = [], []
    for i, (value, start, _) in enumerate(ts):
        if i <= body or i in excluded: continue
        line = first_line + text.count("\n", 0, start)
        if value == "(" or (value in ("[", "{") and i and ts[i - 1][0] == "!"):
            name = invocation_name(ts, i, pairs)
            if name: calls.append({"callee": name, "line": line, "offset": start})
        if value in ("for", "while", "loop"):
            end = next(j for j in range(i + 1, len(ts)) if ts[j][0] == "{")
            header = " ".join(t[0] for t in ts[i:end])
            loops.append({"header": header, "line": line, "offset": start})
    return calls, loops, attrs


def classify(record, policy):
    expected_calls = policy.get("calls", {})
    expected_loops = policy.get("loops", {})
    actual_calls = collections.Counter(call["callee"] for call in record["calls"])
    actual_loops = collections.Counter(loop["header"] for loop in record["loops"])
    if set(actual_calls) != set(expected_calls):
        raise ValueError(f"unclassified/removed calls {record['id']}: {sorted(set(actual_calls) ^ set(expected_calls))}")
    if set(actual_loops) != set(expected_loops):
        raise ValueError(f"unclassified/removed loops {record['id']}: {sorted(set(actual_loops) ^ set(expected_loops))}")
    for name, count in actual_calls.items():
        entry = expected_calls[name]
        if entry.get("count") != count or entry.get("class") not in CLASSES or not entry.get("obligation"):
            raise ValueError(f"bad invocation classification/count: {record['id']}::{name}")
    for name, count in actual_loops.items():
        entry = expected_loops[name]
        if entry.get("count") != count or entry.get("class") not in LOOP_CLASSES or not entry.get("obligation"):
            raise ValueError(f"bad loop classification/count: {record['id']}::{name}")
    if sha(record.pop("text").encode()) != policy["fragment_sha256"]:
        raise ValueError(f"source span changed: {record['id']}")
    record["call_classifications"] = expected_calls
    record["loop_classifications"] = expected_loops


def sdk_pin(entry, registry):
    source = registry / "src" / "index.crates.io-1949cf8c6b5b557f" / entry["source"]
    archive = registry / "cache" / "index.crates.io-1949cf8c6b5b557f" / f"{entry['package']}-{entry['version']}.crate"
    data = source.read_bytes()
    if sha(data) != entry["source_sha256"] or sha(archive.read_bytes()) != entry["package_checksum"]:
        raise ValueError(f"SDK source/archive mismatch: {entry['source']}")
    with tarfile.open(archive) as tf:
        member = tf.extractfile(entry["source"])
        if member is None or member.read() != data: raise ValueError(f"SDK unpacked source mismatch: {source}")
    return {**entry, "source_matches_archive": True, "archive_matches_checksum": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy", type=Path, default=DEFAULT_POLICY)
    parser.add_argument("--registry-root", type=Path, default=Path.home() / ".cargo/registry")
    parser.add_argument("--inventory", action="store_true", help="draft unclassified inventory; never a closure claim")
    parser.add_argument("--write", type=Path, help="write reproducible audit JSON after validating policy")
    parser.add_argument("--check", type=Path, help="compare a saved audit JSON with the current reproducible result")
    parser.add_argument("--require-closed-effects", action="store_true")
    args = parser.parse_args()
    policy = json.loads(args.policy.read_text())
    revision = policy["revision"]
    if not re.fullmatch(r"[0-9a-f]{40}", revision): raise ValueError("full source revision required")
    sources = {path: git_bytes(revision, path) for path in policy["source_files"]}
    for path, expected in policy["source_files"].items():
        if sha(sources[path]) != expected: raise ValueError(f"repository source changed: {path}")
    records = []
    for item in policy["items"]:
        text, start, end, first, last = fragment(sources[item["path"]], item["anchor"])
        calls, loops, attrs = inventory(text, first)
        record = {"id": item["id"], "path": item["path"], "anchor": item["anchor"],
                  "byte_start": start, "byte_end_exclusive": end, "first_line": first, "last_line": last,
                  "fragment_sha256": sha(text.encode()), "calls": calls, "loops": loops,
                  "attributes_in_span": attrs, "text": text}
        if not args.inventory: classify(record, item)
        else: record.pop("text")
        records.append(record)
    if args.inventory:
        print(json.dumps({"status": "UNCLASSIFIED_DRAFT", "items": records}, indent=2))
        return 0
    ids = {r["id"] for r in records}
    for item in policy["items"]:
        for call in item["calls"].values():
            if call["class"] == "expanded" and call.get("target") not in ids:
                raise ValueError(f"expanded target absent: {item['id']}")
    sdk = [sdk_pin(entry, args.registry_root) for entry in policy["sdk_pins"]]
    lock = sources[policy["sdk_lockfile"]].decode()
    for entry in sdk:
        stanza = f'name = "{entry["package"]}"\nversion = "{entry["version"]}"'
        at = lock.find(stanza)
        if at < 0 or f'checksum = "{entry["package_checksum"]}"' not in lock[at:lock.find("\n\n", at)]:
            raise ValueError(f"SDK package/checksum absent from lockfile: {stanza}")
    opaque = [{"item": item["id"], "callee": name, "obligation": call["obligation"]}
              for item in policy["items"] for name, call in item["calls"].items() if call["class"] == "opaque"]
    opaque_loops = [{"item": item["id"], "header": name, "obligation": loop["obligation"]}
                    for item in policy["items"] for name, loop in item["loops"].items() if loop["class"] == "opaque"]
    report = {"status": "PINNED_LEXICAL_AUDIT_ONLY_EFFECT_CLOSURE_OPEN", "revision": revision,
              "configuration": policy["configuration"], "source_files": policy["source_files"],
              "sdk_pins": sdk, "items": records, "opaque_call_obligations": opaque,
              "opaque_loop_obligations": opaque_loops,
              "preservation_obligations": policy["preservation_obligations"],
              "universal_source_cap_proved": False, "cfg_generated": False,
              "generator_sha256": sha(Path(__file__).read_bytes()), "policy_sha256": sha(args.policy.read_bytes())}
    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.check and args.check.read_text() != encoded: raise ValueError("saved audit differs")
    if args.write: args.write.write_text(encoded)
    print(json.dumps({"status": report["status"], "source_items": len(records),
                      "opaque_call_obligations": len(opaque), "cfg_generated": False,
                      "opaque_loop_obligations": len(opaque_loops),
                      "preservation_obligations": policy["preservation_obligations"],
                      "universal_source_cap_proved": False}, indent=2))
    if args.require_closed_effects:
        print("REFUSED: opaque effects and Rust/runtime preservation remain OPEN", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.CalledProcessError, KeyError) as error:
        print(f"FAIL CLOSED: {error}", file=sys.stderr)
        raise SystemExit(1)
