from NMX_formal import *
jobs=['NMX_PdaMap','NMX_EmittedFolded','NMX_InverseScalars','NMX_ErrorCarrier',
 'NMX_InverseSlice','NMX_MasterValue','NMX_CheckpointValue','NMX_AllocationSound',
 'NMX_BoxProjection','NMX_AllocationBoundary','NMX_ArrayEqualityCarrier','NMX_U64Seed',
 'NMX_DistinctValues','NMX_DistinctSuccess','NMX_CanonicalDistinct','NMX_DistinctCarrier',
 'NMX_InputDomain','NMX_RawChildren']
for i,m in enumerate(jobs,159):
 a=f'NMX_L{i:03d}'
 try:r=run(a,'lean',m)
 except AssertionError as e:
  if str(e).startswith('Compile current direct import first:'):
   with (E/'NMX_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(kind='blocked_dependency',attempt=a,module=m,reason=str(e)))+'\n')
   print(json.dumps(dict(attempt=a,module=m,status='not submitted',reason=str(e))),flush=True)
   continue
  raise
