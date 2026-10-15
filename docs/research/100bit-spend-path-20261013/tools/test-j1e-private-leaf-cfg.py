#!/usr/bin/env python3
"""Negative importer checks; no Rust/Lean/toolchain build."""
import copy
import importlib.util
import json
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location("leafcfg", Path(__file__).with_name("j1e-private-leaf-cfg.py"))
cfg = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cfg)


class ImportTests(unittest.TestCase):
    def setUp(self):
        self.document = json.loads((cfg.EVIDENCE / "PrivateLeaf.ullbc").read_text())
        self.source = (cfg.EVIDENCE / "source/state_only_private_merkle.rs").read_text()
        self.blocks = self.document["translated"]["fun_decls"][0]["body"]["Unstructured"]["body"]

    def reject(self):
        with self.assertRaises(ValueError):
            cfg.import_graph(self.document, self.source)

    def test_real_graph_all_statement_and_exit_positions(self):
        graph = cfg.import_graph(self.document, self.source)
        self.assertEqual((graph["node_count"], len(graph["edges"])), (52, 51))
        self.assertEqual(len(graph["import_trace"]), 52)
        self.assertEqual(graph["edges"].count([34, 1, 51]), 1)
        self.assertIn([51, 0, 35], graph["edges"])
        self.assertIn([51, 0, 40], graph["edges"])
        self.assertFalse(any(s in (39, 50) for s, _, _ in graph["edges"]))
        # Check every non-synthetic trace pointer against the original AST.
        for record in graph["import_trace"]:
            if record["pointer"] is None:
                continue
            node = self.document
            for key in record["pointer"].split("/")[1:]:
                node = node[int(key)] if isinstance(node, list) else node[key]
            self.assertEqual(record["ast_sha256"], cfg.sha(cfg.canonical(node)))

    def test_changed_unwind_target_rejected(self):
        self.blocks[0]["terminator"]["kind"]["Call"]["on_unwind"] = 2
        self.reject()

    def test_unknown_call_edge_field_rejected(self):
        self.blocks[0]["terminator"]["kind"]["Call"]["failure"] = 1
        self.reject()

    def test_unknown_statement_rejected(self):
        self.blocks[1]["statements"][0]["kind"] = {"Call": {}}
        self.reject()

    def test_unknown_rvalue_rejected(self):
        self.blocks[0]["statements"][2]["kind"]["Assign"][1] = {"OpaqueEffect": {}}
        self.reject()

    def test_removed_cleanup_rejected(self):
        self.blocks[1]["statements"].pop()
        self.reject()

    def test_unknown_abort_rejected(self):
        self.blocks[1]["terminator"]["kind"] = {"Abort": "NewAbortKind"}
        self.reject()

    def test_callback_argument_substitution_rejected(self):
        self.blocks[0]["statements"][2]["kind"]["Assign"][1]["Use"][0]["Copy"]["kind"] = {"Local": 2}
        self.reject()

    def test_unknown_loop_edge_rejected(self):
        self.blocks[2]["terminator"]["kind"] = {"Goto": 0}
        self.reject()

    def test_source_body_difference_rejected(self):
        self.source = self.source.replace("hash(&[&[DOM_LEAF", "hash(&[&[0")
        self.reject()

    def test_wrong_extraction_configuration_rejected(self):
        self.document["translated"]["options"]["precise_drops"] = False
        self.reject()

    def test_prefixes_can_stop_pending_before_return_or_abort(self):
        graph = cfg.import_graph(self.document, self.source)
        pending = [(0, 0)]
        seen = set()
        while pending:
            node, count = pending.pop()
            self.assertNotIn((node, count), seen)
            seen.add((node, count))
            self.assertLessEqual(count, 1)
            pending.extend((dst, count + cost) for src, cost, dst in graph["edges"] if src == node)
        self.assertIn((51, 1), seen)
        self.assertIn((39, 1), seen)
        self.assertIn((50, 1), seen)
        self.assertEqual(len(seen), 52)


if __name__ == "__main__":
    unittest.main()
