#!/usr/bin/env python3
"""Small negative tests for the lexical audit, not Rust semantic validation."""
import copy
import importlib.util
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location(
    "audit", Path(__file__).with_name("j1e-source-effect-audit.py")
)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class AuditTests(unittest.TestCase):
    def baseline(self):
        text = "fn probe() { for i in 0..3 { hash(&[input]); } }"
        calls, loops, attrs = audit.inventory(text, 1)
        record = {"id": "probe", "text": text, "calls": calls, "loops": loops}
        policy = {
            "fragment_sha256": audit.sha(text.encode()),
            "calls": {"hash": {"count": 1, "class": "designated_hash", "obligation": "OPEN callback binding"}},
            "loops": {"for i in 0 .. 3": {"count": 1, "class": "fixed_range", "obligation": "OPEN iterator lowering"}},
        }
        return record, policy

    def test_literals_comments_and_unary_not_are_not_calls(self):
        text = 'fn p() { /* hash(x); /* loop {} */ */ let s = br#"evil() {"#; if !(false) { good(); } }'
        calls, loops, _ = audit.inventory(text, 1)
        self.assertEqual([c["callee"] for c in calls], ["good"])
        self.assertEqual(loops, [])

    def test_calls_generics_callback_and_macro_delimiters(self):
        text = 'fn p() { f::<u8>(g()); (self.hash)(&[x]); v![h()]; w!{j()}; }'
        calls, _, _ = audit.inventory(text, 1)
        self.assertEqual([c["callee"] for c in calls],
                         ["f", "g", "callable::(self.hash)", "macro::v", "h", "macro::w", "j"])

    def test_cfg_alternatives_are_retained_and_labelled(self):
        calls, _, attrs = audit.inventory('fn p() { #[cfg(feature="x")] a(); #[cfg(not(feature="x"))] b(); }', 1)
        self.assertEqual([c["callee"] for c in calls], ["a", "b"])
        self.assertEqual(len(attrs), 2)

    def test_reviewed_inventory_checks_without_closure_claim(self):
        record, policy = self.baseline()
        audit.classify(record, policy)
        self.assertEqual(record["call_classifications"]["hash"]["class"], "designated_hash")

    def test_unknown_call_fails(self):
        record, policy = self.baseline()
        record["calls"].append({"callee": "surprise", "line": 1, "offset": 0})
        with self.assertRaisesRegex(ValueError, "unclassified/removed calls"):
            audit.classify(record, policy)

    def test_unknown_loop_fails(self):
        record, policy = self.baseline()
        record["loops"].append({"header": "loop", "line": 1, "offset": 0})
        with self.assertRaisesRegex(ValueError, "unclassified/removed loops"):
            audit.classify(record, policy)

    def test_changed_multiplicity_fails(self):
        record, policy = self.baseline()
        record["calls"].append(copy.deepcopy(record["calls"][0]))
        with self.assertRaisesRegex(ValueError, "classification/count"):
            audit.classify(record, policy)

    def test_source_change_without_new_call_fails(self):
        record, policy = self.baseline()
        record["text"] += " "
        with self.assertRaisesRegex(ValueError, "source span changed"):
            audit.classify(record, policy)


if __name__ == "__main__":
    unittest.main()
