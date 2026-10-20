#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
p=Path(__file__).resolve().parent
base=(p/'sources/S3ActualLoop1OuterWholePrefixV1.lean').read_text()
expected=(base.replace('namespace AspisR1GroupedPairActualFieldOpsV3.ActualLoop1OuterPrefix\n','namespace AspisR1GroupedPairActualFieldOpsV3.ActualLoop1OuterPrefixPublic\n').replace('end AspisR1GroupedPairActualFieldOpsV3.ActualLoop1OuterPrefix\n','end AspisR1GroupedPairActualFieldOpsV3.ActualLoop1OuterPrefixPublic\n').replace('private def actualSelectedPrefix','def actualSelectedPrefix').replace('private def actualGroupTerm','def actualGroupTerm').replace('private def actualOuterPrefix','def actualOuterPrefix'))
actual=(p/'sources/S3ActualLoop1OuterWholePrefixPublicV1.lean').read_text()
if expected!=actual:
 print('FAIL: public owner differs beyond namespace/private-to-public recurrence visibility');sys.exit(1)
manifest=json.loads((p/'manifest.json').read_text())
for rel,want in manifest['files'].items():
 f=p/rel
 if not f.is_file() or hashlib.sha256(f.read_bytes()).hexdigest()!=want: print('FAIL file hash',rel);sys.exit(1)
print('PASS: public recurrence owner is exact source copy with only namespace and three private-to-public visibility edits')
