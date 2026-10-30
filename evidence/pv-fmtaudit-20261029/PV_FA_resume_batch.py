"""Consume remaining source-inspection budget; retire every attempted ID."""
from pathlib import Path
import json, subprocess, sys, time
H = Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029')
modules = ['Aeneas/Std/Scalar/Display', 'Aeneas/Std/Scalar/Fmt',
           'Aeneas/Std/Core/FmtWithSlice', 'Aeneas/Std/Core/Panic',
           'Aeneas/Std/Core/Pin', 'Aeneas/Std/Core/Atomic',
           'Aeneas/Command/Decompose/TestsRec',
           'Aeneas/Tactic/Step/StepArraySpec', 'Aeneas/Std/Global']
used = {int(p.name.split('-')[1]) for p in H.iterdir()
        if p.is_dir() and len(p.name.split('-')) > 1
        and p.name.split('-')[1].isdigit()}
next_id = 73758
for module in modules:
    while True:
        while next_id in used:
            next_id += 1
        assert next_id < 73797
        attempt = next_id
        used.add(attempt)
        next_id += 1
        cooldown = H / 'admission-not-before.json'
        while cooldown.exists():
            delay = json.loads(cooldown.read_text())['epoch'] - time.time()
            if delay <= 0:
                break
            time.sleep(min(30, delay))
        rc = subprocess.run([sys.executable, str(H / 'PV_FA_launch.py'),
                             'pincompile', str(attempt), module], cwd=H).returncode
        if rc == 78:
            # User's resume instruction supersedes m': never reuse an ID.
            continue
        if rc:
            sys.exit(rc)
        break
