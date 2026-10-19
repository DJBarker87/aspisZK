#!/usr/bin/env python3
"""Verify exact current sources against focused receipts; never imply full closure."""
from pathlib import Path
import argparse, hashlib, json, re, resource, subprocess, sys, time

started=time.monotonic()
repo=Path(__file__).resolve().parents[5]
area=repo/'docs/research/100bit-spend-path-20261013'
evidence=area/'evidence/cu-equivalence-20261019'
ap=argparse.ArgumentParser();ap.add_argument('--add',nargs=2,action='append',default=[])
ap.add_argument('--pending',action='append',default=[]);a=ap.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
audit_path=evidence/'COMPONENT-AUDIT.json'
audit=json.loads(audit_path.read_text())
pending=audit.setdefault('pending_targets',{})
for module in a.pending:
    source=area/'lean'/(module+'.lean')
    pending[module]=dict(source_sha256=sha(source),status='NOT_COMPILED')
for module,attempt in a.add:
    receipt_path=evidence/attempt/'receipt.json'
    receipt=json.loads(receipt_path.read_text())
    audit['successful_targets'][module]=dict(attempt=attempt,
        source_sha256=receipt['source_sha256'],receipt_sha256=sha(receipt_path))
    pending.pop(module,None)
for module,item in pending.items():
    assert sha(area/'lean'/(module+'.lean'))==item['source_sha256'],module
    assert module not in audit['successful_targets'],module
for module,item in audit['successful_targets'].items():
    source=area/'lean'/(module+'.lean')
    receipt_path=evidence/item['attempt']/'receipt.json'
    receipt=json.loads(receipt_path.read_text())
    assert sha(source)==item['source_sha256']==receipt['source_sha256'],module
    assert sha(receipt_path)==item['receipt_sha256'],module
    assert receipt['exit_status']==0,module
    assert 'sorryAx' not in receipt['print_axioms_output'],module
    assert 'error:' not in receipt['print_axioms_output'],module
    axioms={name.strip() for block in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',
        receipt['print_axioms_output']) for name in block.split(',')}
    extra=axioms-{'propext','Classical.choice','Quot.sound'}
    # Unwrap's Debug instance refers to the backend's opaque Formatter TYPE.
    # Record this conservative carrier boundary; never whitelist a proposition
    # asserting an optimization or a verifier equivalence.
    expected={'core.fmt.Formatter'} if module in {
        'AspisR1CuPrefix/Funs','CuSavingsPrefix','CuSavingsQueryPrefix',
        'AspisR1CuDots/Funs','CuSavingsDotsSlot','CuSavingsDotsSameBytes',
        'CuSavingsDotsBaseStep','CuSavingsDotsBaseProgress','CuSavingsDotsBase',
        'CuSavingsDotsBatches','CuSavingsDotsTail','CuSavingsDotsSlotPrefix'} else set()
    assert extra==expected,(module,extra,expected)
    item['nonstandard_axioms']=sorted(extra)
    assert receipt['process_swaps']==0,module
    if receipt.get('resource_scope')=='focused_local':
        assert receipt['cgroup_swap_bytes'] is None,module
        assert receipt['stopped_for_limit'] is False,module
        assert 0 < receipt['peak_aggregate_rss_bytes_sampled'] < 7*2**30,module
        assert '-M7000' in receipt['command'],module
        assert receipt['mathlib_revision']=='81a5d257c8e410db227a6665ed08f64fea08e997',module
    else:
        assert receipt['cgroup_swap_bytes']==0,module
for name in ['Types.lean','Funs.lean']:
    assert (area/'lean/AspisR1CuRho'/name).read_bytes()==(
        Path(__file__).parent/'rho-generated-pushvalue/AspisR1CuRho'/name).read_bytes(),name
finish_check=subprocess.check_output([sys.executable,str(Path(__file__).with_name('emit-finish.py')),
    '--check'],text=True)
audit['finish_emission_layout_check']=json.loads(finish_check)
finish_source_check=subprocess.check_output([sys.executable,
    str(Path(__file__).with_name('emit-finish-source.py')),'--check'],text=True)
audit['finish_source_emission_layout_check']=json.loads(finish_source_check)
s2_table_check=subprocess.check_output([sys.executable,
    str(Path(__file__).with_name('emit-s2-tables.py')),'--check'],text=True)
audit['s2_table_layout_check']=json.loads(s2_table_check)
audit['iterator_source_checks']={}
for script in ['extract-iterator.py','extract-borrow-option.py','emit-iterator.py']:
    output=subprocess.check_output([sys.executable,str(Path(__file__).with_name(script)),
        '--check'],text=True)
    audit['iterator_source_checks'][script]=json.loads(output)
for directory,source in [('AspisR1CuIterator','iterator-generated'),
                         ('AspisR1CuBorrowOption','borrow-option-generated')]:
    assert (area/'lean'/directory/'Types.lean').read_bytes()==(
        Path(__file__).parent/source/'Types.lean').read_bytes(),directory
audit['rho_init_row_check']=json.loads(subprocess.check_output([
    sys.executable,str(Path(__file__).with_name('extract-rho-init-row.py')),'--check'],text=True))
for name in ['Types.lean','Funs.lean']:
    assert (area/'lean/AspisR1CuRhoInitRow'/name).read_bytes()==(
        Path(__file__).parent/'rho-init-row-generated'/name).read_bytes(),name
audit['cu_prefix_check']=json.loads(subprocess.check_output([
    sys.executable,str(Path(__file__).with_name('extract-cu-prefix.py')),'--check'],text=True))
for name in ['Types.lean','Funs.lean']:
    assert (area/'lean/AspisR1CuPrefix'/name).read_bytes()==(
        Path(__file__).parent/'cu-prefix-generated'/name).read_bytes(),name
audit['cu_query_check']=json.loads(subprocess.check_output([
    sys.executable,str(Path(__file__).with_name('extract-cu-query.py')),'--check'],text=True))
for name in ['Types.lean','Funs.lean']:
    assert (area/'lean/AspisR1CuQuery'/name).read_bytes()==(
        Path(__file__).parent/'cu-query-generated'/name).read_bytes(),name
regression=json.loads((evidence/'nojoin-regression-emission-a/summary.json').read_text())
assert regression['exit_status']==0
assert len(regression['cases'])==4
for case in regression['cases']:
    assert case['exit_status']==0 and case['process_swaps']==0
    assert case['byte_identical'] and case['actual_files']==case['expected_files']
audit['no_branch_join_regression_sha256']=sha(evidence/'nojoin-regression-emission-a/summary.json')
audit['cu_dots_source_check']=json.loads(subprocess.check_output([
    sys.executable,str(Path(__file__).with_name('extract-cu-dots.py')),'--check'],text=True))
audit['cu_dots_emission_check']=json.loads(subprocess.check_output([
    sys.executable,str(Path(__file__).with_name('emit-cu-dots.py')),'--check'],text=True))
usage=resource.getrusage(resource.RUSAGE_SELF)
audit['audit_command']=[sys.executable,str(Path(__file__).relative_to(repo)),*sys.argv[1:]]
audit['audit_source_revision']=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
audit['audit_wall_seconds']=time.monotonic()-started
audit['audit_peak_rss_bytes']=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024
audit['audit_process_swaps']=usage.ru_nswap
audit['audit_exit_status']=0
audit['audit_print_axioms']='N/A: receipt/source audit only; per-target axioms outputs checked above'
audit['full_goal_complete']=False
audit_path.write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps(dict(status=audit['status'],checked_targets=len(audit['successful_targets']),full_goal_complete=False)))
