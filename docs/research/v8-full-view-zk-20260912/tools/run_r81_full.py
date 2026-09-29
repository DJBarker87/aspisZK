#!/usr/bin/env python3
"""Release checks and complete SBF comparison against unchanged R19 proofs."""
from pathlib import Path
import json, shutil, sys
here=Path(__file__).parent
mode=sys.argv[sys.argv.index('--mode')+1]
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
resources={n:(cg/n).read_text().strip()for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
high,maximum={'host':(5,7),'sbf':(12,16),'svm':(2,3)}[mode]
assert resources=={'memory.high':str(high*2**30),'memory.max':str(maximum*2**30),'memory.swap.max':'0','pids.max':'128'}
resources['cgroup']=str(cg)
source=(here/'run_r69_full.py').read_text()
source=source.replace("+(5 if 'r69_explicit_product'in m else 0)",
    "+(5 if 'r69_explicit_product'in m else 0)+(5 if 'r81_native'in m else 0)+(2 if m.get('r81_native',{}).get('variant') in ['powerbasis','compose','privatebasis','scalarg'] else 0)+(1 if m.get('r81_native',{}).get('variant') in ['privatebasis','scalarg'] else 0)")
source=source.replace("    assert 'r69_explicit_product' in m", """    assert 'r81_native' in m
    if m['r81_native']['variant'] in ['powerbasis','compose','privatebasis','scalarg']:
        run('basis-compile.log',['/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--manifest-path',str(ex/'performance-host/Cargo.toml'),'--features',meta['features'],'--bin','r81-basis-check'])
        run('basis-check.log',[str(cache/'release/r81-basis-check')])
    run('square-compile.log',['/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--manifest-path',str(ex/'performance-host/Cargo.toml'),'--features',meta['features'],'--bin','r81-square-check'])
    run('square-check.log',[str(cache/'release/r81-square-check')])
    assert 'r69_explicit_product' in m""")
exec(compile(source,str(here/'run_r69_full.py'),'exec'))
(out/'resources.json').write_text(json.dumps(resources,indent=2)+'\n')
if a.mode=='sbf':
    unstripped=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-sbf/target/sbpf-solana-solana/release/aspis_v8_performance_sbf.so')
    shutil.copy2(unstripped,s/'aspis-unstripped.so')
