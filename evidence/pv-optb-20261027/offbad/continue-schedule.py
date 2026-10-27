import ast,pathlib
from step import append
m='R1Z/PV_OptB_AlignedSchedule';ns='R1Z.PV_OptB_AlignedSchedule'
s=pathlib.Path('evidence/pv-optb-20261027/offbad/schedule-steps.py').read_text()
exec(s[s.index("append(m,ns,'rejection_aligned'"):])
