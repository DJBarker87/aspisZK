#!/usr/bin/env python3
"""diagnostic, not a V374 measurement; static instruction inventory, no kernel calls."""
import subprocess,pathlib,re,json,hashlib
B=pathlib.Path('/home/dombarker/project-offloads/codex-pv-dudect-20261027')
identity={}
for label,p in [('harness',B/'bin/pv-dudect'),('candidate',B/'bin/devnet_spend'),('diagnostic',B/'harness-target/release/diagnostic')]:
 raw=subprocess.check_output(['objdump','-d','-C','-M','intel','--no-show-raw-insn',str(p)],text=True)
 selected=[];keep=False
 for l in raw.splitlines():
  m=re.match(r'^([0-9a-f]+) <(.+)>:$',l)
  if m:keep=any(s in m[2] for s in ['host_hashv','sha2::sha256::compress256','sha2::sha256::x86::digest_blocks','SeedExpander::qm31','state_only_hiding::measure_m31','state_only_hiding::measure_qm31','state_only_hiding::sample_mask_cells'])
  if keep:selected.append(l)
 (B/'diagnosis-trace'/(label+'-seed-path.asm')).write_text('\n'.join(selected)+'\n')
 identity[label]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
identity['cpuinfo']=pathlib.Path('/proc/cpuinfo').read_text().split('\n\n')[0]
identity['quiet_marker_exists']=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json').exists()
identity['temperature_after_diagnostics']=pathlib.Path('/sys/class/thermal/thermal_zone5/temp').read_text().strip()
print(json.dumps(identity,indent=2))
