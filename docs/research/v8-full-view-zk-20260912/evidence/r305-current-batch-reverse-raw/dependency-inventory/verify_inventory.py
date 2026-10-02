#!/usr/bin/env python3
"""Verify saved R292 loop block identity and external-template direct-reference scan."""
import hashlib,json,pathlib,re
HERE=pathlib.Path(__file__).resolve().parent
WORKTREE=HERE.parents[1]
FUNS=WORKTREE/'.r21-scratch/r292-private-batch-translation/generated/AspisR292PrivateBatch/Funs.lean'
MANIFEST=WORKTREE/'.r21-scratch/r292-private-batch-translation/generated/translation.json'
RAW=HERE/'inventory.json'
rec=json.loads(RAW.read_text())
assert hashlib.sha256(FUNS.read_bytes()).hexdigest()==rec['provenance']['Funs_sha256']
assert hashlib.sha256(MANIFEST.read_bytes()).hexdigest()==rec['provenance']['translation_json_sha256']
assert rec['provenance']['embedded_r110_norm_sha256']==rec['provenance']['expected_frozen_r110_norm_sha256']
for key in ('loop2_body','loop3_body'):
 row=rec['generated_definition_blocks'][key]
 assert hashlib.sha256((HERE/row['path']).read_bytes()).hexdigest()==row['sha256']
assert rec['generated_definition_blocks']['normalized_bodies_equal'] is True
assert all(v is False for v in rec['external_template_check']['six_rejected_templates_directly_referenced_in_loop_body'].values())
assert all(v is False for v in rec['external_template_check']['type_template_referenced_in_loop_body'].values())
print('R304 saved loop inventory verified')
