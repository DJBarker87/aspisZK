"""Offline causal audit of captured cross-platform limit validation failure.

No host access, bootstrap re-execution, operational repair, or GO replay.
"""
import ast
import json
from pathlib import Path
import resource
import shlex
import subprocess
import sys
import ResourceRssGOv2_local as local
import ResourceRssGOv2_host as host
import ResourceRssGOv2_sources as sources

OUT=local.OUT
HERE=Path(__file__).resolve().parent

def main():
    transport=json.loads((OUT/'inspect-transport.json').read_text())
    info=json.loads((OUT/'runtime-inspection.json').read_text())
    seal=json.loads((OUT/'ResourceRssGOv2-preparation-seal.json').read_text())
    mapping=json.loads((OUT/'ResourceRssGOv2-identity-mapping.json').read_text())
    assert transport['exit']==0 and not transport['stderr']
    assert json.loads(transport['stdout'])==info
    assert info['inherited_limits']['RLIMIT_AS']==[-1,-1]
    assert info['inherited_limits']['RLIMIT_DATA']==[-1,-1]
    assert resource.RLIM_INFINITY != -1
    assert not info['stage_exists'] and info['uid']==info['parent_uid']==1000
    argv=shlex.split(transport['command'][-1])
    assert argv[:4]==['/usr/bin/python3','-I','-B','-c'] and len(argv)==5
    assert host.digest(argv[-1].encode())==seal['bootstrap_payload']
    assert argv[-1]==local.inspection_payload()
    initial=host.inherited_limits()
    error=None
    try:host.check_limits(info['inherited_limits'])
    except host.GuardError as exc:error=str(exc)
    assert error=='unexpected inherited restriction: RLIMIT_AS'
    assert host.inherited_limits()==initial
    for name,record in mapping['files'].items():
        raw=(HERE/name).read_bytes()
        assert host.digest(raw)==record['after']
        normalized=raw.decode()
        for old,new in reversed(mapping['renames']):normalized=normalized.replace(new,old)
        assert host.digest(normalized.encode())==record['before']
        assert normalized.encode()==(OUT/(name+'.before.py.txt')).read_bytes()
    for name,pin in seal['sources'].items():
        raw=(json.dumps(sources.bundle(),sort_keys=True,indent=2)+'\n').encode() if name=='ResourceRssGOv2_reviewed.json' else (HERE/name).read_bytes()
        assert host.digest(raw)==pin
        if name!='ResourceRssGOv2_reviewed.json':
            assert subprocess.check_output(['git','show',transport['source_revision']+':tools/resource-rss-go-v2-20261025/'+name],cwd=local.ROOT)==raw
    assert (OUT/'ATTEMPTED').exists()
    absent=['manifest.json','RUN_ATTEMPTED','stage-transport.json','stage-preflight-transport.json','run-transport.json','prospective-ordered.json','scope-argv.json','marker.json','export-receipt.json']
    assert all(not (OUT/n).exists() for n in absent)
    tree=ast.parse((HERE/'ResourceRssGOv2_local.py').read_text())
    fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='inspect')
    assert ast.unparse(fn.body[0])=='charge()'
    assert ast.unparse(fn.body[-2])=="save('runtime-inspection.json', info)"
    assert ast.unparse(fn.body[-1])=="host.check_limits(info['inherited_limits'])"
    result=dict(status='PASS offline causal failure audit',source_revision=local.revision(),
        executed_source_revision=transport['source_revision'],charged='USED1/1 before sole SSH; four prior failures remain charged',
        exact_error=error,local_RLIM_INFINITY=resource.RLIM_INFINITY,host_AS=info['inherited_limits']['RLIMIT_AS'],host_DATA=info['inherited_limits']['RLIMIT_DATA'],
        cause='Darwin checker compares Linux infinity -1 against Darwin RLIM_INFINITY; host limits are NOT finite',
        host_ssh_exit=transport['exit'],local_inspect_exit=1,host_wall_seconds=transport['wall_seconds'],
        host_peak_rss='N/A unmeasured inspection',host_swap='N/A unmeasured inspection',
        source_mapping='exact normalized byte and AST mapping retained; executed committed source matches seal',
        bootstrap='executed successfully; returned runtime and complete inherited limits before local rejection',
        runtime=host.filepin(OUT/'runtime-inspection.json'),transport=host.filepin(OUT/'inspect-transport.json'),
        local_limit_check_reproduced=True,no_resource_limit_mutation=True,
        prospective=False,stage=False,scope=False,GO=False,marker=False,
        GO_ordered_input_replay='N/A no prospective/GO inputs or reports; this is only causal failure audit',
        absent_evidence=absent,followup_host_operations=0,axioms='N/A',
        both_deployed_targets='not established',native_proof_compiler_budgets='all unused zero; private Kani59/60 final1 RESERVED')
    with (OUT/'ResourceRssGOv2-terminal-audit.json').open('x') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps(result,sort_keys=True))
if __name__=='__main__':main()
