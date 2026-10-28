from pathlib import Path
import os,json,stat
p=Path('/home/dombarker/project-offloads/codex-cx-native-elfscope-20261028/NCR_B003/artifacts/aspis_r1_cost_probe_program-keypair.json')
assert p.is_file() and not p.is_symlink()
before=stat.S_IMODE(p.stat().st_mode);os.chmod(p,0o600)
print(json.dumps({'retained_key_path':str(p),'mode_before':oct(before),'mode_after':oct(stat.S_IMODE(p.stat().st_mode)),'key_contents_read':False,'key_deleted':False,'fund_or_authority_action':'none'}))
