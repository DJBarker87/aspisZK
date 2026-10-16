#!/usr/bin/env python3
"""Add an atomic prelaunch check after hashing; monitor only active Lean jobs."""
from pathlib import Path
import shutil
W=Path('/home/dombarker/project-offloads/aspis-r1-public-binding-followup-20261016')
p=W/'runner.py';original=W/'tools/runner-before-guard.py';assert original.is_file();s=original.read_text()
helper='''
def external_lean(own=None):
    processes = {}
    for path in Path('/proc').iterdir():
        if not path.name.isdigit():
            continue
        try:
            parent = int((path / 'stat').read_text().split(') ', 1)[1].split()[1])
            processes[int(path.name)] = (parent, (path / 'exe').resolve().name)
        except (OSError, RuntimeError, ValueError):
            pass
    def child(pid):
        seen = set()
        while pid in processes and pid not in seen:
            if pid == own:
                return True
            seen.add(pid)
            pid = processes[pid][0]
        return False
    own_cgroup = Path('/proc/self/cgroup').read_text()
    def different_cgroup(pid):
        try:
            return Path('/proc', str(pid), 'cgroup').read_text() != own_cgroup
        except OSError:
            return False
    return [pid for pid, (_, exe) in processes.items() if exe == 'lean' and different_cgroup(pid)]

'''
s=s.replace('VERSION = "4.32.0"',helper+'VERSION = "4.32.0"',1)
needle='''            proc = subprocess.Popen(cmd, cwd=external["lake_cwd"], env=env,
'''
assert s.count(needle)==1
s=s.replace(needle,'''            # Import hashing may overlap external work; Lean itself may not.
            while external_lean():
                time.sleep(0.2)
            begin = time.monotonic()
            proc = subprocess.Popen(cmd, cwd=external["lake_cwd"], env=env,
''',1)
needle='''                peak = max(peak, int(read(cg / "memory.current")))
'''
assert s.count(needle)==1
s=s.replace(needle,'''                arrivals = external_lean(proc.pid)
                if arrivals:
                    print("STOP OWN LEAN external=" + repr(arrivals), flush=True)
                    os.killpg(proc.pid, signal.SIGKILL)
                    stopped = True
                    break
                peak = max(peak, int(read(cg / "memory.current")))
''',1)
p.write_text(s)
print('Own runner guarded after import hashing and monitored during actual Lean; no accepted workspace modified')
