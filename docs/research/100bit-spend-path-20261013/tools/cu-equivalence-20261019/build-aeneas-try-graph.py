#!/usr/bin/env python3
"""Build an isolated opt-in checked Try graph metadata extension.

Never edits either previously pinned frontend. Docker's compile gate stays
closed until memory.high/max/swap=6/8/0 GiB are verified on its actual cgroup.
Run this controller through the ordinary capped receipt runner as well.
"""
from pathlib import Path
import argparse,difflib,hashlib,json,os,re,subprocess,time

sha=lambda b:hashlib.sha256(b).hexdigest()
def run(args,**kwargs):return subprocess.run(args,check=True,**kwargs)
def reservations():
    finite=[]
    for file in Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            value=file.read_text().strip()
            if value!='max' and 'populated 1' in (file.parent/'cgroup.events').read_text():
                finite.append((str(file.parent),int(value)))
        except OSError:pass
    return [(p,n) for p,n in finite if not any(p.startswith(q+'/') for q,_ in finite if q!=p)]
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--output-name',default='aeneas-try-graph')
    args=ap.parse_args();root=args.root
    assert args.output_name.startswith('aeneas-try-graph') and '/' not in args.output_name
    out=root/args.output_name
    before_reservations=reservations()
    assert sum(n for _,n in before_reservations)+8*2**30<=50*2**30,('NOT_LAUNCHED',before_reservations)
    out.mkdir(exist_ok=False)
    base=root/'aeneas-trait-constraints-reservation-checked/aeneas'
    run(['cp','-a','--reflink=auto',str(base),str(out/'aeneas')])
    file=out/'aeneas/src/extract/ExtractBuiltinLean.ml';before=file.read_text()
    runtime='AspisR1.CuSavingsTryGraphRuntime.'
    flag='Sys.getenv_opt "AENEAS_R1_TRY_GRAPH" = Some "1"'
    old='mk_trait_decl "core::ops::try_trait::Residual" "core.ops.try_trait.Residual"'
    replacement='mk_trait_decl "core::ops::try_trait::Residual" (if '+flag+' then "'+runtime+'Residual" else "core.ops.try_trait.Residual")'
    assert before.count(old)==1;after=before.replace(old,replacement,1)
    old='mk_trait_decl "core::ops::try_trait::Try" "core.ops.try_trait.Try"\n      ~parent_clauses:[ "FromResidualInst" ]'
    replacement='mk_trait_decl "core::ops::try_trait::Try" (if '+flag+' then "'+runtime+'DynamicTry" else "core.ops.try_trait.Try")\n      ~parent_clauses:(if '+flag+' then [ "FromResidualInst"; "ResidualInst" ] else [ "FromResidualInst" ])\n      ~types:(if '+flag+' then [("Output", "Output"); ("Residual", "Residual"); ("Self_Clause1_TryType", "Self_Clause1_TryType")] else [])'
    assert after.count(old)==1;after=after.replace(old,replacement,1)
    addition=Path(__file__).with_name('aeneas-try-graph-metadata.ml').read_text()
    after+='\n'+addition;file.write_text(after)
    patch=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),
        fromfile='a/src/extract/ExtractBuiltinLean.ml',tofile='b/src/extract/ExtractBuiltinLean.ml'))
    (out/'try-graph-metadata.patch').write_text(patch)
    build=(root/'aeneas-trait-constraints-reservation-checked/build.sh').read_text().replace(
        '+parent-projection-constraints-20261019','+r1-try-graph-20261019')
    (out/'build.sh').write_text(build)
    pins=dict(base_binary_sha256=sha((root/'aeneas-trait-constraints-reservation-checked/bin/aeneas').read_bytes()),
        original_source_sha256=sha(before.encode()),patched_source_sha256=sha(after.encode()),
        patch_sha256=sha(patch.encode()),build_script_sha256=sha(build.encode()),
        controller_sha256=sha(Path(__file__).read_bytes()),helper_sha256=sha(addition.encode()),
        source_path='src/extract/ExtractBuiltinLean.ml',
        scope='Opt-in metadata binds retained Try associated types and both parents to concrete checked graph adapters. Only the two concrete cyclic infallible instances and empty residual type receive checked builtin models. No interpreter/type/borrow check change.')
    image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
    command=['docker','create','--name','aspis-cu-'+args.output_name+'-20261019',
        '--network','none','--read-only','--memory','8g','--memory-swap','8g',
        '--pids-limit','128','--cap-drop','ALL','--security-opt','no-new-privileges',
        '--tmpfs','/tmp:rw,nosuid,size=256m','--mount',f'type=bind,src={out}/aeneas,dst=/work/aeneas',
        '--mount','type=bind,src=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon,dst=/work/charon,readonly',
        '--mount',f'type=bind,src={out},dst=/out','--entrypoint','/bin/bash',image,'/out/build.sh']
    container=run(command,stdout=subprocess.PIPE,text=True).stdout.strip()
    run(['docker','start',container],stdout=subprocess.PIPE)
    pid=run(['docker','inspect','--format','{{.State.Pid}}',container],stdout=subprocess.PIPE,text=True).stdout.strip()
    cg=Path('/sys/fs/cgroup')/Path('/proc',pid,'cgroup').read_text().split('0::',1)[1].strip().lstrip('/')
    try:
        run(['sudo','-n','tee',str(cg/'memory.high')],input=str(6*2**30),text=True,stdout=subprocess.PIPE)
        limits={name:(cg/name).read_text().strip() for name in ['memory.high','memory.max','memory.swap.max']}
        assert limits=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'},limits
        admitted=reservations()
        assert sum(n for _,n in admitted)<=50*2**30,('NOT_LAUNCHED',admitted)
        preflight=dict(command=command,container=container,image=image,cgroup=str(cg),limits=limits,pins=pins,
            reservations_before_create=before_reservations,reservations_at_compile_gate=admitted,
            expected_work='Incremental optimized OCaml build from copied Dune objects; no Rust/sysroot/Lean replay.',
            print_axioms='N/A: frontend build')
        (out/'preflight.json').write_text(json.dumps(preflight,indent=2)+'\n')
        (out/'compile-go').touch();started=time.monotonic();peak=0;last={}
        while True:
            state=json.loads(run(['docker','inspect','--format','{{json .State}}',container],stdout=subprocess.PIPE,text=True).stdout)
            if not state['Running']:break
            current_reservations=reservations()
            assert sum(n for _,n in current_reservations)<=50*2**30,('STOP_FOR_RESERVATION_REVIEW',current_reservations)
            try:
                last={name:(cg/name).read_text().strip() for name in ['memory.current','memory.peak','memory.swap.current','memory.events']}
                peak=max(peak,int(last['memory.current']))
                assert last['memory.swap.current']=='0'
                assert peak < 8*2**30 and time.monotonic()-started<180
            except FileNotFoundError:pass
            time.sleep(.2)
        assert state['ExitCode']==0,state
        timing=(out/'compile-time.log').read_text()
        def metric(name):return int(re.search(re.escape(name)+r':\s*(\d+)',timing)[1])
        receipt=dict(preflight,exit_status=state['ExitCode'],wall_seconds=time.monotonic()-started,
            peak_rss_kib=metric('Maximum resident set size (kbytes)'),process_swaps=metric('Swaps'),
            sampled_cgroup_peak_bytes=peak,last_cgroup_observation=last,
            binary_sha256=sha((out/'bin/aeneas').read_bytes()))
        (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(receipt))
    except BaseException:
        run(['docker','stop','--time','1',container],stdout=subprocess.PIPE)
        raise

if __name__=='__main__':main()
