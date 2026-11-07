from NMX_formal import *
for i,m in enumerate(['NMX_LEApi','NMX_SeedFrames','NMX_DistinctPredicate','NMX_SemanticF04'],269):
 try:r=run(f'NMX_L{i:03d}','lean',m)
 except AssertionError as e:
  if str(e).startswith('Compile current direct import first:'):
   with (E/'NMX_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(kind='blocked_dependency',attempt=f'NMX_L{i:03d}',module=m,reason=str(e)))+'\n')
   print(str(e),flush=True)
  else:raise
