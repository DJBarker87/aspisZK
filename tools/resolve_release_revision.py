#!/usr/bin/env python3
"""Resolve published Git identities after the documented privacy rewrite."""
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MAPPING_PATH = ROOT / "release/history-redaction-map.json"
MAPPING = json.loads(MAPPING_PATH.read_text())
OBJECTS = MAPPING["commits"] | MAPPING["trees"]


def resolve(value):
    """Translate only a full object ID, retaining any Git revision suffix."""
    return re.sub(r"^[0-9a-f]{40}(?=$|[:^~])",
                  lambda match: OBJECTS.get(match[0], match[0]), value)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: resolve_release_revision.py OBJECT_ID")
    print(resolve(sys.argv[1]))
