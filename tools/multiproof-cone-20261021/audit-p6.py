#!/usr/bin/env python3
"""Fail-closed review of helper certificates and the whole-function attempts."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT/'docs/research/100bit-spend-path-20261013'
E = PACKET/'evidence/multiproof-cone-20261021'
T = ROOT/'tools/multiproof-cone-20261021'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_text())

def function(text, marker):
    start = text.index(marker); end = text.index('{', start)+1; depth=1
    while depth:
        depth += (text[end]=='{')-(text[end]=='}'); end+=1
    return text[start:end]

def success(path, count):
    r=load(path/'receipt.json')
    assert r['exit_status']==0 and r['swaps']==0
    output=(path/'stdout.log').read_text()
    assert output.count('VERIFICATION SUCCESSFUL')==count and 'VERIFICATION FAILED' not in output
    if 'kani_verifier_validation' in r:
        assert r['kani_verifier_validation']=={'expected_harnesses':count,
            'successful_verifier_results':count,'failed_verifier_results':0,'complete':True}
    assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),
                         'memory.swap.max':'0','pids.max':'64'}
    return r

for script in ['generate.py','p6-citations.py']:
    subprocess.run(['python3','-B',str(T/script),'--check'],check=True)

callbacks=E/'host-p6/p6-callbacks-1'
callback=success(callbacks,3)
for relative in ['tools/multiproof-cone-20261021/src/p6_callbacks.rs',
                 'tools/multiproof-cone-20261021/src/adoption_node.rs']:
    assert sha(ROOT/relative)==callback['source_sha256'][relative]
# Only the whole-verifier tape construction changed after the helper gate.
marker='/// Independent oracle replies'
assert (callbacks/'inputs/src--p6_certificates.rs.txt').read_text().split(marker)[0]==\
    (T/'src/p6_certificates.rs').read_text().split(marker)[0]

observer=success(E/'host/receipts/cone3-hash-1',1)
assert sha(T/'src/adoption_node.rs')==observer['source_sha256']['tools/multiproof-cone-20261021/src/adoption_node.rs']
leaf_path=E/'host/receipts/cone2-leaf-2'
leaf=success(leaf_path,2)
assert sha(T/'src/adoption.rs')==leaf['source_sha256']['tools/multiproof-cone-20261021/src/adoption.rs']
assert function((leaf_path/'inputs/src--frozen.rs.txt').read_text(),'pub(crate) fn batch_leaf<')==\
    function((T/'src/frozen.rs').read_text(),'pub(crate) fn batch_leaf<')
for relative in ['crates/aspis-core/src/digest.rs',
                 'crates/aspis-core/src/state_only_private_merkle.rs','crates/aspis-core/src/r0/merkle.rs']:
    assert sha(ROOT/relative)==leaf['source_sha256'][relative]

read_path=E/'host/receipts/final-read32-contract-1'
reader=success(read_path,1)
assert sha(T/'src/reference.rs')==reader['source_sha256']['tools/multiproof-cone-20261021/src/reference.rs']

endpoint=load(E/'MultiproofConeFrozen2Stage-2/receipt.json')
assert endpoint['exit']==0 and endpoint['swaps']==0
assert endpoint['source_sha256']==sha(PACKET/'lean/MultiproofConeFrozen2Stage.lean')
for line in endpoint['axioms']:
    match=re.search(r'axioms: \[(.*?)\]',line)
    assert match and {x.strip() for x in match[1].split(',')}<={'propext','Classical.choice','Quot.sound'}

attempts=[]
for name in ['p6-verifier-1','p6-verifier-2','p6-verifier-3']:
    folder=E/'host-p6'/name
    r=load(folder/'receipt.json')
    assert r['exit_status']!=0 and not r['kani_verifier_validation']['complete']
    assert r['swaps']==0
    if name=='p6-verifier-3':
        for relative in ['tools/multiproof-cone-20261021/src/p6_certificates.rs',
                         'tools/multiproof-cone-20261021/src/frozen.rs',
                         'tools/multiproof-cone-20261021/src/reference.rs']:
            assert sha(ROOT/relative)==r['source_sha256'][relative]
        assert r['kani_verifier_validation']['successful_verifier_results']==0
        assert 'VERIFICATION SUCCESSFUL' not in (folder/'stdout.log').read_text()
    attempts.append({k:r[k] for k in ['attempt','target','source_revision','deps_fingerprint',
        'exit_status','raw_tool_exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms',
        'kani_verifier_validation','cgroup_memory_peak_bytes','limits']})

changes=subprocess.check_output(['git','diff','--name-only','57ca9c452'],cwd=ROOT,text=True).splitlines()
assert not any(p.startswith('crates/') or '/lean/' in p or '/lean-candidates/' in p for p in changes)
result={'schema':'multiproof-p6-focused-audit-v1','source_revision':subprocess.check_output(
    ['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    'new_callback_contracts':callback,'verified_observer_callee_reused':observer,
    'leaf_hash_certificate_reused':leaf,'verified_read32_callee_reused':reader,
    'retained_stage_lean_receipt':endpoint,'whole_verifier_attempts':attempts,
    'source_batch_certificate_supplied':False,'whole_verifier_certificate_supplied':False,
    'stage_instantiation_permitted':False,'headline_premises_removed':0,
    'shipped_and_all_lean_sources_unchanged':True,'elf_rebuild_triggered':False,
    'new_lean_print_axioms':'N/A: no Lean declaration added; endpoint axiom reports reused above'}
(E/'p6-audit-result.json').write_text(json.dumps(result,indent=2)+'\n')
print('Three node callback contracts current; whole-source stage instantiation blocked')
