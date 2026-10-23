#!/usr/bin/env python3
"""Validate and summarize retained evidence; never launches another build."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parent.parent
lean = Path('docs/research/v8-r0-zk-20261009/lean')
attempts = []
for directory in sorted((root/'lean').iterdir()):
    if (directory/'preflight.json').exists():
        attempts.append(dict(attempt=int(directory.name),**json.loads((directory/'preflight.json').read_text())))
        continue
    receipt = json.loads((directory/'receipt.json').read_text())
    assert hashlib.sha256((directory/'source.lean.txt').read_bytes()).hexdigest() == receipt['source_sha256']
    if receipt['exit_status'] == 0:
        for line in receipt['axioms']:
            names = set(re.search(r'\[([^]]*)\]',line)[1].replace(' ','').split(','))
            assert names <= {'propext','Classical.choice','Quot.sound'}, line
    attempts.append({k:receipt[k] for k in ['attempt','module','source_revision','source_sha256',
                                          'deps_fingerprint','exit_status','axioms','time_log']})

final = json.loads((root/'lean/10914/receipt.json').read_text())
assert final['exit_status'] == 0 and len(final['axioms']) == 13
checks = []
for dep in final['deps']:
    path = lean/(dep['module'].replace('.','/')+'.lean')
    if not path.exists():
        continue
    local = path.read_bytes()
    local_hash = hashlib.sha256(local).hexdigest()
    row = dict(module=dep['module'],local_sha256=local_hash,host_sha256=dep['source_sha256'],
               exact_source_equal=local_hash==dep['source_sha256'])
    if not row['exact_source_equal']:
        host = (root/'dependency-audit'/('RealR1_'+str(path.relative_to(lean)).replace('/','_')+'.host.txt')).read_bytes()
        assert hashlib.sha256(host).hexdigest() == dep['source_sha256']
        migrated = local.replace(b'import ImportUnionNamedDiscriminant\n',b'').replace(b'import_union_discriminant',b'discriminant')
        row['equal_after_only_discriminant_import_migration'] = migrated == host
        assert migrated == host, dep['module']
    checks.append(row)
(root/'dependency-audit/source-comparison.json').write_text(json.dumps(checks,indent=2)+'\n')

native=[]
for directory in sorted((root/'native').iterdir()):
    receipt=json.loads((directory/'receipt.json').read_text())
    pins=json.loads((directory/'inputs.json').read_text())
    assert hashlib.sha256((directory/'RealR1_reservation.rs.txt').read_bytes()).hexdigest()==pins['files']['RealR1_reservation.rs']
    native.append(dict(name=directory.name,**receipt,inputs=pins))
    if directory.name.endswith('-v4'):
        assert receipt['exit_status']==0
        assert 'SUCCESSFUL' in (directory/'stdout.log').read_text()
        assert receipt['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
        for name,expected in pins['files'].items():
            assert hashlib.sha256((root/'harness'/name).read_bytes()).hexdigest()==expected

caller=json.loads((root/'caller-gate.json').read_text())
assert caller['exit_status']==1 and caller['checks']['actual_96byte_retry_call']
assert not caller['checks']['selected_retry_call'] and not caller['checks']['selected_64byte_factory']

record=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
            lean_compiles=sum('exit_status' in a for a in attempts),lean_preflight_refusals=2,
            kani_commands=len(native),lean_budget=100,kani_budget=60,final_axiom_reports=len(final['axioms']),
            lean=attempts,native=native,caller_gate=caller,
            dependency_sources_compared=len(checks),dependency_migration_only_differences=[r for r in checks if not r['exact_source_equal']],
            target_established=False,scope='Conditional reference real outer owner; no complete native experiment or deployment instance.',
            artifacts='No shipped sources changed; no ELF rebuild; no new binary identity claimed.')
(root/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['lean_compiles','kani_commands','final_axiom_reports','dependency_sources_compared','target_established']}))
