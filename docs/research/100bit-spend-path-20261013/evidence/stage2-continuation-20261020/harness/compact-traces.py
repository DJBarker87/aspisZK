#!/usr/bin/env python3
"""Retain full host debug traces by SHA; publish compact failure excerpts."""
from pathlib import Path
import hashlib,json
B=Path(__file__).resolve().parents[1]
H='/home/dombarker/project-offloads/codex-cx-stage2b-20261020/receipts'
for p in (B/'attempts').glob('*/extract-*/stdout.log'):
 raw=p.read_bytes()
 if len(raw)<=200000:continue
 pin=dict(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),retained_host_path=H+'/'+p.parent.name+'/stdout.log',excerpt='stdout-tail.log contains the final 60000 bytes; stderr.log is retained in full')
 (p.parent/'stdout-pin.json').write_text(json.dumps(pin,indent=2)+'\n')
 (p.parent/'stdout-tail.log').write_text(raw[-60000:].decode('utf-8','replace'));p.unlink()
