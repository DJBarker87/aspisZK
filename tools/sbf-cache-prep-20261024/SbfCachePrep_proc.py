#!/usr/bin/env python3
"""Read-only privileged proc metadata. No subprocesses, donor opens or writes."""
import hashlib,json,os,pathlib,resource,sys,time
ROOTS=tuple('/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023/'+s for s in ('sbf-target-verifier','sbf-target-pool'))
LIMIT=1024*1024

def member(s):
    # Deleted fd links still retain their path; cmdline match is conservative.
    return any(r in s for r in ROOTS)

def identity(raw):
    # comm may itself contain spaces and parentheses. Fields after final ')'.
    tail=raw.rsplit(')',1)[1].split()
    return dict(pid=int(raw.split(' ',1)[0]),state=tail[0],flags=int(tail[6]),starttime=int(tail[19]))

def bounded(path):
    with path.open('rb') as f:
        b=f.read(LIMIT+1)
    if len(b)>LIMIT:raise ValueError('metadata exceeds bound')
    return b

def inspect(d):
    before=identity(bounded(d/'stat').decode());row=dict(identity=before,errors=[],matches=[])
    try:
        status=bounded(d/'status').decode();fields=dict(line.split(':',1) for line in status.splitlines() if ':' in line)
        row['status']={k:fields[k].strip() for k in ('State','Tgid','Pid','PPid','Uid','Gid','Threads')}
        cmd=bounded(d/'cmdline');row['cmdline_sha256']=hashlib.sha256(cmd).hexdigest();row['cmdline_bytes']=len(cmd)
        row['cgroup_sha256']=hashlib.sha256(bounded(d/'cgroup')).hexdigest()
        kernel=bool(before['flags'] & 0x200000) and not cmd and int(fields['Pid'])==before['pid']
        row['classification']='kernel-thread' if kernel else 'userspace'
        if member(cmd.decode(errors='replace')):row['matches'].append('cmdline')
        for name in ('cwd','exe'):
            try:
                target=os.readlink(d/name)
                if member(target):row['matches'].append(name)
            except FileNotFoundError:
                if not kernel:raise
        row['fd_count']=0
        # Keep directory stream open while inspecting its entries. Materializing
        # then closing it makes our own /proc fd entry disappear artificially.
        with os.scandir(d/'fd') as entries:
            for entry in entries:
                row['fd_count']+=1
                if row['fd_count']>20000:raise ValueError('fd bound exceeded')
                fd=pathlib.Path(entry.path);target=os.readlink(fd)
                info=bounded(d/'fdinfo'/fd.name).decode()
                flags=[line.split(':',1)[1].strip() for line in info.splitlines() if line.startswith('flags:')]
                if len(flags)!=1:raise ValueError('missing fd flags')
                flag=int(flags[0],8)
                if member(target):row['matches'].append(dict(fd=int(fd.name),access_mode=flag & os.O_ACCMODE,donor=True))
    except (OSError,ValueError,KeyError) as e:row['errors'].append(type(e).__name__)
    try:
        after=identity(bounded(d/'stat').decode());row['identity_stable']=before==after
        # State may change normally, but PID/starttime/flags identity must agree.
        row['identity_stable']=all(before[k]==after[k] for k in ('pid','starttime','flags'))
    except (OSError,ValueError) as e:
        row['identity_stable']=False;row['errors'].append('vanished-or-unreadable-after:'+type(e).__name__)
    return row

def observe(proc):
    initial=sorted(int(p.name) for p in proc.iterdir() if p.name.isdecimal())
    if len(initial)>20000:raise ValueError('process bound exceeded')
    rows=[]
    for pid in initial:
        try:
            leader=proc/str(pid)
            # Real proc has per-thread tables; fixture absence is not accepted.
            tids=sorted(int(p.name) for p in (leader/'task').iterdir() if p.name.isdecimal())
            if pid not in tids or len(rows)+len(tids)>20000:raise ValueError('thread set/bound')
            for tid in tids:
                row=inspect(leader/'task'/str(tid));row['tgid']=pid;rows.append(row)
            after=sorted(int(p.name) for p in (leader/'task').iterdir() if p.name.isdecimal())
            if tids!=after:rows.append(dict(pid=pid,errors=['thread-set-race'],identity_stable=False))
        except (OSError,ValueError) as e:rows.append(dict(pid=pid,errors=['vanished-or-unreadable-before:'+type(e).__name__],identity_stable=False))
    final=sorted(int(p.name) for p in proc.iterdir() if p.name.isdecimal())
    allowed=initial==final and all(r['identity_stable'] and not r['errors'] and not r.get('matches') for r in rows)
    return dict(allowed_to_enter=allowed,processes=rows,initial_pids=initial,final_pids=final,process_set_stable=initial==final,cache_hash_or_copy_run=False,limitation='Sequential metadata only; no exclusion against future exec/open, no atomic snapshot or TOU proof')

def main():
    resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));start=time.monotonic()
    try:
        r=observe(pathlib.Path('/proc'));exit_code=0
    except Exception as e:r=dict(allowed_to_enter=False,error=type(e).__name__);exit_code=1
    u=resource.getrusage(0)
    r['observer_pid']=os.getpid()
    r['receipt']=dict(command=['sudo','-n','python3','-'],exit=exit_code,wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A',runtime=sys.version)
    output=json.dumps(r,sort_keys=True)
    if len(output)>16*1024**2:output=json.dumps(dict(allowed_to_enter=False,error='output bound exceeded'));exit_code=1
    print(output);return exit_code
if __name__=='__main__':sys.exit(main())
