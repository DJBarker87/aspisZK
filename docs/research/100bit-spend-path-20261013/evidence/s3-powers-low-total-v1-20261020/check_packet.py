#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, sys

packet = Path(__file__).resolve().parent
repo = packet.parents[4]
manifest = json.loads((packet / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
for rel, expected in manifest['evidence_files'].items():
    path = packet / rel
    assert path.is_file(), f'missing packet file: {rel}'
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    assert actual == expected, f'packet hash mismatch: {rel}: {actual}'
for rel, expected in manifest['direct_import_source_map'].items():
    source = repo / expected['repository_path']
    assert source.is_file(), f'missing direct import source: {rel}'
    actual = hashlib.sha256(source.read_bytes()).hexdigest()
    assert actual == expected['source_sha256'], f'direct source hash mismatch: {rel}'
    receipt = repo / expected['producer_receipt_path']
    assert receipt.is_file(), f'missing producer receipt: {rel}'
    actual = hashlib.sha256(receipt.read_bytes()).hexdigest()
    assert actual == expected['producer_receipt_sha256'], f'producer receipt hash mismatch: {rel}'
assert manifest['modules'][0]['exit_status'] == 0
assert manifest['modules'][0]['axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
print('PASS: packet files, direct source owners, producer receipts, and standard axiom record')
