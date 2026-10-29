"""Recover the candidate's original project-only V229 checker, no credit upgrade.
The old script's final print assumes --finalize; omit only that display line.
Do not execute its historical native receipt acceptance against deployed sources.
"""
from pathlib import Path
import sys,hashlib,json
R=Path(__file__).resolve().parents[2];p=R/'tools/pv-b3p6-20261028/structural133.py'
raw=p.read_text();last="print(json.dumps(dict(exact_body_copies=len(records),row_closed=record['row_closed'],native_link_credit=record['native_link_credit'])))"
assert raw.count(last)==1
code=raw.replace(last,'')
old=Path.write_text
E=R/'evidence/pv-rdb2d-20261028'
def write(p,s,*args,**kw):
 assert p==R/'evidence/pv-b3p6-20261028/structural133.json',str(p)
 j=json.loads(s);j.update(row_closed=False,native_link_credit=False,recovered_from=str(p),original_checker_sha256=hashlib.sha256(raw.encode()).hexdigest(),recovery_change='omit only final display indexing missing row_closed when --finalize is absent',scope='project body/certificate checks only; deployed std body laws and full row closure remain suspended')
 return old(E/'V229-project-check.json',json.dumps(j,indent=2)+'\n')
Path.write_text=write
sys.argv=[str(p),'--check']
exec(compile(code,str(p),'exec'),{'__file__':str(p),'__name__':'__main__'})
print('V229 original project body/certificate checker recovered and passed; no deployed row credit')
