from NLA_pda import attempt
n=31
for case in range(6):
 for field in range(2):
  if case==0 and field==0:continue
  for mode in ['positive','inverse']:
   r=attempt(f'NLA_K{n:03}',case,field,mode);n+=1
   assert r['exit_status']==(0 if mode=='positive' else 1)
