from NLA_registry import attempt
n=8
for part in ['prefix','address']:
 for mode in ['positive','inverse']:
  r=attempt(f'NLA_K{n:03}',part,mode);n+=1
  assert r['exit_status']==(0 if mode=='positive' else 1)
for version in [1,2]:
 for entry in [False,True]:
  for field in range(2):
   for mode in ['positive','inverse']:
    r=attempt(f'NLA_K{n:03}','data',mode,version,entry,field);n+=1
    assert r['exit_status']==(0 if mode=='positive' else 1)
