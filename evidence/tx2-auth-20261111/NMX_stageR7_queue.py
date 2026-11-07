from NMX_formal import *
jobs=['NMX_InspectByte','NMX_CommandTransport','NMX_SemanticTail05','NMX_DistinctStep']+[f'NMX_DistinctWindow{k}' for k in range(7)]
for i,m in enumerate(jobs,248):
 try:run(f'NMX_L{i:03d}','lean',m)
 except AssertionError as e:
  if str(e).startswith('Compile current direct import first:'):
   with (E/'NMX_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(kind='blocked_dependency',attempt=f'NMX_L{i:03d}',module=m,reason=str(e)))+'\n')
   print(str(e),flush=True)
  else:raise
