#!/usr/bin/env python3
"""Run authoritative NDT tests unchanged; redirect only their output receipt."""
import runpy
from pathlib import Path
from unittest.mock import patch
import NEN_validate as v

original = Path.write_text
allowed = v.R / 'evidence/native-ledger3-20261029/NDT_TEST_RECEIPT.json'

def write_receipt(path, contents, *args, **kwargs):
    if path.resolve() != allowed:
        raise AssertionError('Unexpected inherited test write: ' + str(path))
    return original(v.E / 'NEN_INHERITED_TEST_RECEIPT.json', contents, *args, **kwargs)

with patch.object(Path, 'write_text', write_receipt):
    runpy.run_path(str(v.R / 'evidence/native-ledger3-20261029/NDT_tests.py'), run_name='__main__')
