#!/usr/bin/env python3
"""Build an isolated opt-in identical-associated-type matcher repair.

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
    args=ap.parse_args();root=args.root;out=root/'aeneas-associated-types'
    out.mkdir(exist_ok=False)
    base=root/'aeneas-no-branch-join/aeneas'
    run(['cp','-a','--reflink=auto',str(base),str(out/'aeneas')])
    file=out/'aeneas/src/interp/InterpMatchCtxs.ml';before=file.read_text()
    anchor='  | TSlice ty0, TSlice ty1 -> TSlice (match_rec ty0 ty1)\n'
    assert before.count(anchor)==1
    addition='''  | TTraitType _, TTraitType _
    when Sys.getenv_opt "AENEAS_IDENTICAL_ASSOCIATED_TYPES" = Some "1"
         && phys_eq ty0 ty1 && ty_no_regions ty0 ->
      (* Identical region-free projections require no alpha-renaming map.
         Distinct projections and every projection containing a region keep
         the existing matching path. No iteration or borrow check is skipped. *)
      ty0
'''
    after=before.replace(anchor,anchor+addition,1);file.write_text(after)
    patch=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),
        fromfile='a/src/interp/InterpMatchCtxs.ml',tofile='b/src/interp/InterpMatchCtxs.ml'))
    (out/'associated-types.patch').write_text(patch)
    build=(root/'aeneas-no-branch-join/build.sh').read_text().replace(
        '+no-branch-join-20261019','+identical-associated-types-20261019')
    (out/'build.sh').write_text(build)
    pins=dict(base_binary_sha256=sha((root/'aeneas-no-branch-join/bin/aeneas').read_bytes()),
        original_source_sha256=sha(before.encode()),patched_source_sha256=sha(after.encode()),
        patch_sha256=sha(patch.encode()),build_script_sha256=sha(build.encode()),
        controller_sha256=sha(Path(__file__).read_bytes()),
        source_path='src/interp/InterpMatchCtxs.ml',
        scope='Opt-in exact physical equality of region-free associated types only; no region renaming, distinct-type acceptance, iteration increase, or skipped checks.')
    image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
    command=['docker','create','--name','aspis-cu-aeneas-associated-types-20261019',
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
