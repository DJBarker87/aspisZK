#!/usr/bin/env python3
"""Build an isolated source-constraint normalization repair.

Never edits either previously pinned frontend. Docker's compile gate stays
closed until memory.high/max/swap=6/8/0 GiB are verified on its actual cgroup.
Run this controller through the ordinary capped receipt runner as well.
"""
from pathlib import Path
import argparse,difflib,hashlib,json,os,re,subprocess,time

sha=lambda b:hashlib.sha256(b).hexdigest()
def run(args,**kwargs):return subprocess.run(args,check=True,**kwargs)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
    args=ap.parse_args();root=args.root;out=root/'aeneas-trait-constraints'
    out.mkdir(exist_ok=False)
    base=root/'aeneas-associated-types/aeneas'
    run(['cp','-a','--reflink=auto',str(base),str(out/'aeneas')])
    file=out/'aeneas/src/interp/InterpUtils.ml';before=file.read_text()
    anchor='let instantiate_fun_sig (span : Meta.span option) (ctx : eval_ctx)\n'
    assert before.count(anchor)==1
    helper=Path(__file__).with_name('aeneas-parent-projection-constraints.ml').read_text()
    after=before.replace(anchor,helper+'\n'+anchor,1)
    old='  let output = st_substitute_visitor#visit_ty subst output in\n\n  (* Compute the regions hierarchy *)'
    new='  let output = st_substitute_visitor#visit_ty subst output in\n  let inputs = List.map (normalize_parent_projection_constraints ctx) inputs in\n  let output = normalize_parent_projection_constraints ctx output in\n\n  (* Compute the regions hierarchy *)'
    assert after.count(old)==1;after=after.replace(old,new,1);file.write_text(after)
    patch=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),
        fromfile='a/src/interp/InterpUtils.ml',tofile='b/src/interp/InterpUtils.ml'))
    (out/'trait-constraints.patch').write_text(patch)
    build=(root/'aeneas-associated-types/build.sh').read_text().replace(
        '+identical-associated-types-20261019','+parent-projection-constraints-20261019')
    (out/'build.sh').write_text(build)
    pins=dict(base_binary_sha256=sha((root/'aeneas-associated-types/bin/aeneas').read_bytes()),
        original_source_sha256=sha(before.encode()),patched_source_sha256=sha(after.encode()),
        patch_sha256=sha(patch.encode()),build_script_sha256=sha(build.encode()),
        controller_sha256=sha(Path(__file__).read_bytes()),helper_sha256=sha(helper.encode()),
        source_path='src/interp/InterpUtils.ml',
        scope='Opt-in region-free parent projection normalization using exact instantiated constraints from the source trait declaration; every type/borrow/copy check and every trait constraint retained.')
    image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
    command=['docker','create','--name','aspis-cu-aeneas-trait-constraints-20261019',
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
        preflight=dict(command=command,container=container,image=image,cgroup=str(cg),limits=limits,pins=pins,
            expected_work='Incremental optimized OCaml build from copied Dune objects; no Rust/sysroot/Lean replay.',
            print_axioms='N/A: frontend build')
        (out/'preflight.json').write_text(json.dumps(preflight,indent=2)+'\n')
        (out/'compile-go').touch();started=time.monotonic();peak=0;last={}
        while True:
            state=json.loads(run(['docker','inspect','--format','{{json .State}}',container],stdout=subprocess.PIPE,text=True).stdout)
            if not state['Running']:break
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
