"""Fail closed before any own driver admission within180s of a known refusal."""
from pathlib import Path
from datetime import datetime,timezone
import json

def check():
 ev=Path(__file__).resolve().parents[2]/'evidence/pv-cb-20261026'
 refusals=[]
 for p in ev.glob('*/collected-receipt.json'):
  try:
   r=json.loads(p.read_text())
   for a in r.get('admissions',{}).values():
    if a.get('allowed') is False and a.get('utc'):refusals.append((datetime.fromisoformat(a['utc']),str(p)))
  except (ValueError,TypeError):continue
 if refusals:
  when,path=max(refusals);elapsed=(datetime.now(timezone.utc)-when).total_seconds()
  if elapsed<180:raise SystemExit(f'NO ADMISSION: {elapsed:.6f}s since refusal {path}; need180s')
