#!/usr/bin/env python3
"""Recreate R280 decoded.json from the retained compact Charon LLBC."""
import hashlib
import json
import pathlib
import sys

if len(sys.argv) != 3:
    raise SystemExit(f"usage: {sys.argv[0]} INPUT.llbc OUTPUT.json")
src_path, out_path = map(pathlib.Path, sys.argv[1:])
raw = json.loads(src_path.read_text())
table = {}
stats = {"cycles": 0, "missing_hashcons_ids": 0}

def collect(x):
    if isinstance(x, dict):
        if "HashConsedValue" in x:
            ident, value = x["HashConsedValue"]
            table[ident] = value
            collect(value)
        elif "Deduplicated" not in x:
            for value in x.values():
                collect(value)
    elif isinstance(x, list):
        for value in x:
            collect(value)

def expand(x, seen=()):
    if isinstance(x, dict):
        if "Deduplicated" in x:
            ident = x["Deduplicated"]
            if ident in seen:
                stats["cycles"] += 1
                return {"cycle": ident}
            if ident not in table:
                stats["missing_hashcons_ids"] += 1
                return {"missing_hashcons_id": ident}
            return expand(table[ident], seen + (ident,))
        if "HashConsedValue" in x:
            ident, value = x["HashConsedValue"]
            return expand(value, seen + (ident,))
        return {key: expand(value, seen) for key, value in x.items()}
    if isinstance(x, list):
        return [expand(value, seen) for value in x]
    return x

collect(raw)
expanded = expand(raw)
out = (json.dumps(expanded, indent=2) + "\n").encode()
out_path.write_bytes(out)
print(json.dumps({
    "input_sha256": hashlib.sha256(src_path.read_bytes()).hexdigest(),
    "output_bytes": len(out),
    "output_sha256": hashlib.sha256(out).hexdigest(),
    "hashcons_table_entries": len(table),
    **stats,
}, indent=2))
