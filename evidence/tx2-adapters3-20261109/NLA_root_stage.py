from NLA_lane import attempt
from NLA_formal import run
for a,f,m in [('NLA_K003',0,'inverse'),('NLA_K004',1,'positive'),('NLA_K005',1,'inverse'),('NLA_K006',2,'positive'),('NLA_K007',2,'inverse')]:
 r=attempt(a,f,m)
 if r['exit_status'] not in ([0] if m=='positive' else [1]):raise RuntimeError('Unexpected verdict '+a)
run('NLA_L002','lean','NLA_RootPrefix')
