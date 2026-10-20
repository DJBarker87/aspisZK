#!/usr/bin/env python3
"""Assemble/check an inventory-only focused packet; no proof/build invocation."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[5]
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
OUT=BASE/'evidence/stage2-extraction-20261020'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def manifest():
    historical=[]
    for p in sorted((OUT/'receipts').glob('*.json')):
        if p.name.endswith(('-charon.json','-aeneas.json')):
            r=json.loads(p.read_text())
            historical.append(dict(receipt=str(p.relative_to(OUT)),sha256=sha(p),
                phase=r['phase'],source_revision=r['source_revision'],
                exact_target=r['command'],exit_status=r['exit_status'],
                wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_process_rss_kib'],
                process_swaps=r['process_swaps'],cgroup_swap_current=r['cgroup_swap_current'],
                limits=r['limits'],tool_pins=r['tool_pins'],llbc_pins=r['outputs'],
                axioms='N/A: Charon only or failed Aeneas; no Lean theorem',
                reused_historical_evidence=True,new_execution=False))
    references={}
    for packet in ['stage2-authenticated-wrapper-20261019','stage2-parse-variant-tag-20261019',
        'stage2-authenticated-parser-join-20261020','stage2-reader-cursor-decoder-20261019',
        'stage2-resume-fixed-prefix-20261019','stage2-resume-prefix-canonical-20261020']:
        for f in ['manifest.json','README.md']:
            p=BASE/'evidence'/packet/f
            references[str(p.relative_to(ROOT))]=sha(p)
    for p in [BASE/'design/J1-INTEGRATED-DECLARATION-REPIN-20261016.json',
              BASE/'design/LEAD-REVIEW-FORMAT-ADOPT-20261020.md',
              BASE/'evidence/format-adopt-20261019/artifacts-sha256.txt',
              BASE/'lean-candidates/finish-relation-source-candidate-20261019/verifier-candidate.patch',
              BASE/'lean-candidates/stage2-extraction-frontier-addendum-20261019/attempts/root-stage2-adopted-caller-v2-20261019/boundary-opacity-check.json']:
        references[str(p.relative_to(ROOT))]=sha(p)
    files={str(p.relative_to(OUT)):sha(p) for p in sorted(OUT.rglob('*')) if p.is_file() and p.name!='manifest.json'}
    tools={str(p.relative_to(ROOT)):sha(p) for p in sorted(Path(__file__).parent.iterdir()) if p.is_file()}
    return dict(schema='focused-extractor-proof-packet-v1',
        packet_kind='inventory-only-stop-before-refactor',stage=1,
        source_revision='9a71031d3a95f838ac6d75bd5c58eeafeb62a9e1',
        publication_base_revision='e90cf2f80',modules=[],new_extraction_runs=[],new_lean_runs=[],
        axioms='N/A: no new theorem; predecessor proof axioms remain in referenced manifests',
        status='STOPPED: required pinned Aeneas cannot translate unchanged finish_relation; lead decision required before any verifier refactor',
        inventory_counts=json.loads((OUT/'pins/cone.json').read_text())['counts'],
        reused_historical_receipts=historical,files=files,references=references,tools=tools,
        design={'path':str((BASE/'design/STAGE2-EXTRACTION-20261020.md').relative_to(ROOT)),
                'sha256':sha(BASE/'design/STAGE2-EXTRACTION-20261020.md')},
        requested_host_workspace='/home/dombarker/project-offloads/codex-cx-stage2-20261020',
        host_workspace_used=False,reason_no_runs='Existing exact-root failure with required pins; no unchanged rerun or source refactor authorized.',
        validation_command='python3 -B docs/research/100bit-spend-path-20261013/tools/stage2-extraction-kit/packet.py --check')
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    subprocess.run(['python3','-B',str(Path(__file__).with_name('inventory.py')),'--check'],check=True,cwd=ROOT)
    raw=(json.dumps(manifest(),indent=2,sort_keys=True)+'\n').encode()
    p=OUT/'manifest.json'
    if a.check:assert p.read_bytes()==raw,'packet manifest differs'
    else:p.write_bytes(raw)
    print('Packet check PASS' if a.check else 'Packet assembled')
if __name__=='__main__':main()
