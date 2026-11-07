from NMX_formal import *
jobs=['NMX_SpecAssociativity','NMX_Skeleton','NMX_Semantics','NMX_DenoteStep',
 'NMX_BoxPostProjection','NMX_MasterChild','NMX_CheckpointChild','NMX_BoxCommands',
 'NMX_PdaSound','NMX_SmallIndices','NMX_DistinctSuccess','NMX_DistinctCarrier','NMX_BvByte']
for group in reversed(range(6)):jobs += [f'NMX_SF{group:02d}',f'NMX_CB{group:02d}']
for i,m in enumerate(jobs,208):
 a=f'NMX_L{i:03d}'
 try:r=run(a,'lean',m)
 except AssertionError as e:
  if str(e).startswith('Compile current direct import first:'):
   with (E/'NMX_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(kind='blocked_dependency',attempt=a,module=m,reason=str(e)))+'\n')
   print(json.dumps(dict(attempt=a,module=m,status='not submitted',reason=str(e))),flush=True)
   continue
  raise
