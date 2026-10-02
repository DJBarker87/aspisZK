#!/usr/bin/env python3
"""Tiny synthetic negative checks for comparator guardrails; no LLBC input."""
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("cmp", HERE / "compare_llbc_hardened.py")
cmp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cmp)
checks = []

def must_fail(label, fn, contains):
    try:
        fn()
    except ValueError as e:
        assert contains in str(e), (label, str(e))
        checks.append({"case": label, "result": "rejected", "message": str(e)})
    else:
        raise AssertionError(f"{label} unexpectedly accepted")

# Hash-cons self-cycle must never be replaced by a comparable marker.
cyclic = {"HashConsedValue": [0, {"next": {"Deduplicated": 0}}]}
table = {}
cmp.collect_hashcons(cyclic, table)
must_fail("cyclic hash-cons", lambda: cmp.decode(cyclic, table), "cyclic")
must_fail("malformed wrapper extra key", lambda: cmp.collect_hashcons({"Deduplicated": 1, "extra": 0}, {}), "malformed")
must_fail("malformed hash-cons payload", lambda: cmp.collect_hashcons({"HashConsedValue": [True, {}]}, {}), "nonnegative integer")
must_fail("root replacement", lambda: cmp.validate_edit_paths([{"path": [], "kind": "replace_exact"}]), "root replacement")
must_fail("ancestor overlap", lambda: cmp.validate_edit_paths([
    {"path": ["translated", "fun_decls", 58], "kind": "replace_exact"},
    {"path": ["translated", "fun_decls", 58, "body"], "kind": "replace_exact"},
]), "overlapping")
must_fail("drop without exact resulting list", lambda: cmp.apply_approved_edits({"args": [1, 2]}, [
    {"path": ["args"], "kind": "drop_list_item_exact", "index": 0, "before_item": 1}
]), "requires exact")
# One exact leaf replacement is permitted by the mechanism; all sibling fields survive.
result, records = cmp.apply_approved_edits({"sig": {"ty": "A"}, "body": {"op": "call"}}, [
    {"path": ["sig", "ty"], "kind": "replace_exact", "before": "A", "after": "B"}
])
assert result == {"sig": {"ty": "B"}, "body": {"op": "call"}}
checks.append({"case": "exact leaf replacement preserves sibling executable field", "result": "accepted-as-mechanical-operation-only", "record_count": len(records)})
(HERE / "synthetic-negative-cases.json").write_text(json.dumps({
    "classification": "synthetic guardrail tests only; no actual LLBC transform or semantic acceptance",
    "cases": checks,
}, indent=2) + "\n")
print(json.dumps({"checks": len(checks), "all_negative_cases_rejected": all(x["result"] != "rejected" or x["message"] for x in checks), "receipt": str(HERE / "synthetic-negative-cases.json")}, indent=2))
