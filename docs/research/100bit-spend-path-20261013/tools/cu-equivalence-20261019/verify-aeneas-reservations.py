#!/usr/bin/env python3
"""Recheck the pinned frontend with actual aggregate cgroup admission.

The controller uses a 1GiB cgroup; the compiler retains its separate 6/8/0GiB
limits. No compile gate opens unless all populated reservations total <=50GiB.
No foreign job is stopped or changed.
"""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,time
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
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
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);a=ap.parse_args()
    root=a.root;base=root/'aeneas-trait-constraints';out=root/'aeneas-trait-constraints-reservation-checked'
    out.mkdir(exist_ok=False)
    original=json.loads((base/'receipt.json').read_text())
    assert sha(base/'bin/aeneas')==original['binary_sha256']
    before=reservations()
    assert sum(n for _,n in before)+8*2**30<=50*2**30,('NOT_LAUNCHED',before)
    run(['cp','-a','--reflink=auto',str(base/'aeneas'),str(out/'aeneas')])
    assert sha(out/'aeneas/src/interp/InterpUtils.ml')==original['pins']['patched_source_sha256']
    (out/'build.sh').write_bytes((base/'build.sh').read_bytes())
    image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
    command=['docker','create','--name','aspis-cu-aeneas-trait-constraints-reservation-20261019',
        '--network','none','--read-only','--memory','8g','--memory-swap','8g','--pids-limit','128',
        '--cap-drop','ALL','--security-opt','no-new-privileges','--tmpfs','/tmp:rw,nosuid,size=256m',
        '--mount',f'type=bind,src={out}/aeneas,dst=/work/aeneas',
        '--mount','type=bind,src=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon,dst=/work/charon,readonly',
        '--mount',f'type=bind,src={out},dst=/out','--entrypoint','/bin/bash',image,'/out/build.sh']
    container=run(command,stdout=subprocess.PIPE,text=True).stdout.strip()
    run(['docker','start',container],stdout=subprocess.PIPE)
    try:
        pid=run(['docker','inspect','--format','{{.State.Pid}}',container],stdout=subprocess.PIPE,text=True).stdout.strip()
        cg=Path('/sys/fs/cgroup')/Path('/proc',pid,'cgroup').read_text().split('0::',1)[1].strip().lstrip('/')
        run(['sudo','-n','tee',str(cg/'memory.high')],input=str(6*2**30),text=True,stdout=subprocess.PIPE)
        limits={name:(cg/name).read_text().strip() for name in ['memory.high','memory.max','memory.swap.max']}
        assert limits=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
        admitted=reservations();assert sum(n for _,n in admitted)<=50*2**30,('NOT_LAUNCHED',admitted)
        preflight=dict(command=command,container=container,image=image,cgroup=str(cg),limits=limits,
            reservations_before_create=before,reservations_at_compile_gate=admitted,
            source_revision=original.get('source_revision'),original_frontend_binary_sha256=original['binary_sha256'],
            source_sha256=sha(out/'aeneas/src/interp/InterpUtils.ml'),controller_sha256=sha(Path(__file__)),
            expected_work='Identical cached frontend build with corrected aggregate reservation admission; no source/proof change.',
            print_axioms='N/A: frontend build')
        (out/'preflight.json').write_text(json.dumps(preflight,indent=2)+'\n')
        started=time.monotonic();peak=0;last={};max_reserved=sum(n for _,n in admitted)
        (out/'compile-go').touch()
        while True:
            state=json.loads(run(['docker','inspect','--format','{{json .State}}',container],stdout=subprocess.PIPE,text=True).stdout)
            if not state['Running']:break
            current=reservations();reserved=sum(n for _,n in current);max_reserved=max(max_reserved,reserved)
            assert reserved<=50*2**30,('STOP_FOR_RESERVATION_REVIEW',current)
            try:
                last={name:(cg/name).read_text().strip() for name in ['memory.current','memory.peak','memory.swap.current','memory.events']}
                peak=max(peak,int(last['memory.current']));assert last['memory.swap.current']=='0'
                assert peak<8*2**30 and time.monotonic()-started<180
            except FileNotFoundError:pass
            time.sleep(.2)
        assert state['ExitCode']==0,state
        timing=(out/'compile-time.log').read_text()
        def metric(label):return int(re.search(re.escape(label)+r':\s*(\d+)',timing)[1])
        binary=sha(out/'bin/aeneas');assert binary==original['binary_sha256']
        receipt=dict(preflight,exit_status=0,wall_seconds=time.monotonic()-started,
            peak_rss_kib=metric('Maximum resident set size (kbytes)'),process_swaps=metric('Swaps'),
            sampled_cgroup_peak_bytes=peak,last_cgroup_observation=last,
            max_sampled_reservations_bytes=max_reserved,binary_sha256=binary,
            resource_admission_verified=True)
        (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
    except BaseException:
        run(['docker','stop','--time','1',container],stdout=subprocess.PIPE);raise
if __name__=='__main__':main()
