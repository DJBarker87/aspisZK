#!/usr/bin/env python3
"""New-profile source affine gates, genuine proof generation and full runtime."""
from pathlib import Path
source=Path(__file__).with_name('run_r84_full.py').read_text()
source=source.replace("assert 'r84_compact' in m","assert 'r84_compact' in m and 'r102_auth' in m")
old="    compile('r84-bitperm-check');run('compact-check.log',[str(cache/'release/r84-bitperm-check')])"
new="""    control=Path(m['r102_auth']['control']);cm=json.loads((control/'r18-stage.json').read_text())
    changed=[n for n,h in m['files'].items()if cm['files'].get(n)!=h]
    assert len(changed)==9 and all(n.startswith('docs/research/v8-no-work-100-20260907/experiments/') for n in changed)
    shutil.copy2(control/'r24-host-a/compact-check.log',out/'compact-check.log')
    compile('r102-auth-check');run('auth-check.log',[str(cache/'release/r102-auth-check')])"""
assert source.count(old)==1;source=source.replace(old,new)
source=source.replace("        run(f'generate-world{w}.log',[str(binary),str(f)])", """        # Heavy phase is optimized actual-source witness correction/elimination,
        # followed by complete proof generation; no debug arithmetic gate.
        env['ASPIS_R17_C1_WITNESS_AUDIT']='1'
        run(f'generate-world{w}.log',[str(binary),str(f)])
        env.pop('ASPIS_R17_C1_WITNESS_AUDIT')
        gate=(out/f'generate-world{w}.log').read_text()
        for marker in ['R17_H1_WITNESS_JOINT rank=540','R19_G_WITNESS_JOINT equations=626 rank=602',
          'R19_CHANNEL_WITNESS source_p0_p2_retained=true','R17_C1_WITNESS_VALIDATED same_public=true']:
            assert marker in gate,marker""")
source=source.replace("str(here/'check_r19_wire_controls.py')","str(here/'check_r102_wire_controls.py')")
source=source.replace("'--old-fixture','/home/dombarker/project-offloads/aspis-r19-channel-20260921-c/host-c/fixture-world0'",
    "'--old-fixture',str(Path(m['r85_native']['fixtures'][0]['path'])),'--old-fixture','/home/dombarker/project-offloads/aspis-r19-channel-20260921-c/host-c/fixture-world0'")
source=source.replace("    assert 'compact_source_implemented=true'", "    for w in range(2):assert 'R19_CHANNEL_WITNESS source_p0_p2_retained=true' in (s/f'r24-host-a/generate-world{w}.log').read_text()\n    assert 'compact_source_implemented=true'")
exec(compile(source,str(Path(__file__).with_name('run_r84_full.py')),'exec'))
