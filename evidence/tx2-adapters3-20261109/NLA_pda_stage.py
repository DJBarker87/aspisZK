from NLA_pda import attempt
n=28
for case in range(6):
 for field in range(2):
  for mode in ['positive','inverse']:
   r=attempt(f'NLA_K{n:03}',case,field,mode);n+=1
   assert r['exit_status']==(0 if mode=='positive' else 1)
