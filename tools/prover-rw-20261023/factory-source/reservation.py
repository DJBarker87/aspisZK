"""Full hierarchy plus Docker/service/process visibility and uncapped reserve."""
from pathlib import Path
import json,runpy,subprocess
base=runpy.run_path(str(Path(__file__).with_name('reservation_base.py')))
def admission(requested=8*2**30):
    out=base['admission'](requested=requested)
    try:
        def run(args):
            return subprocess.run(args,check=True,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=15).stdout
        out['process_visibility']=run(['ps','-e','-o','pid,ppid,rss,comm,cgroup'])
        out['service_visibility']=run(['systemctl','list-units','--type=service','--state=running','--no-pager','--no-legend'])
        ids=run(['docker','ps','-q']).split()
        out['docker_visibility']=[json.loads(run(['docker','inspect','--format','{{json .State}}',i]))|{'id':i,'host_config':json.loads(run(['docker','inspect','--format','{{json .HostConfig}}',i]))} for i in ids]
        mem=dict((line.split(':')[0],int(line.split()[1])*1024) for line in Path('/proc/meminfo').read_text().splitlines() if ':' in line and len(line.split())>=2)
        out['meminfo']=mem
        # Exclusive accounting: hierarchical current includes child current.
        # Subtract direct children before summing uncapped groups; this also
        # removes finite-capped subtrees already charged by the base scanner.
        rows=out['cgroups']; bypath={r['path']:r for r in rows}
        exclusive=[]
        for r in out.get('uncapped_background',[]):
            if not r['memory_controller_enabled']: continue
            children=[c for c in rows if Path(c['path']).parent==Path(r['path']) and c.get('memory_controller_enabled')]
            usage=r['memory_current']-sum(c['memory_current'] for c in children)
            # A racing negative value denies instead of silently clipping.
            if usage<0: raise ValueError('hierarchical usage raced: '+r['path'])
            exclusive.append(dict(path=r['path'],exclusive_current_bytes=usage))
        out['uncapped_exclusive_usage']=exclusive
        out['uncapped_current_bytes']=sum(r['exclusive_current_bytes'] for r in exclusive)
        out['os_remote_reserve_bytes']=7*2**30
        out['reserve_check']=out.get('projected_reserved_bytes',2**63)+out['uncapped_current_bytes']+out['os_remote_reserve_bytes']<mem['MemTotal'] and mem['MemAvailable']>requested+2*2**30
        out['allowed']=out['allowed'] and out['reserve_check']
    except (OSError,ValueError,subprocess.SubprocessError) as e:
        out.update(allowed=False,visibility_error=str(e))
    return out
