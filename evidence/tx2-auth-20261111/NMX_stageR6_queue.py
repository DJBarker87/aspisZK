from NMX_formal import *
jobs=['NMX_SpecAssociativity','NMX_Skeleton','NMX_DenoteStep','NMX_BvByte','NMX_U64Byte0','NMX_ScalarBne','NMX_CommandTransport','NMX_IndexTransport','NMX_SeedConstants']
jobs += [f'NMX_SF{g:02d}' for g in reversed(range(6))]
for i,m in enumerate(jobs,233):
 try: run(f'NMX_L{i:03d}','lean',m)
 except AssertionError as e:
  if str(e).startswith('Compile current direct import first:'):
   with (E/'NMX_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(kind='blocked_dependency',attempt=f'NMX_L{i:03d}',module=m,reason=str(e)))+'\n')
   print(str(e),flush=True)
  else:raise
