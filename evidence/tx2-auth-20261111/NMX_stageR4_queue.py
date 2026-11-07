from NMX_formal import *
jobs=[('NMX_L177','NMX_ErrorCarrier'),('NMX_L178','NMX_InverseSlice'),('NMX_L179','NMX_InputDomain'),('NMX_L180','NMX_RawChildren'),('NMX_L181','NMX_Heterogeneous'),('NMX_L182','NMX_HeterogeneousPrimitives'),('NMX_L183','NMX_ResultRelation'),('NMX_L184','NMX_DecoderLibrary'),('NMX_L185','NMX_DecoderErrors'),('NMX_L186','NMX_DistinctValues'),('NMX_L187','NMX_DistinctSuccess'),('NMX_L188','NMX_DistinctCarrier'),('NMX_L189','NMX_QuestionValue'),('NMX_L190','NMX_PdaValue'),('NMX_L191','NMX_U64Seed'),('NMX_L192','NMX_EmittedFolded')]
for a,m in jobs:
 try:r=run(a,'lean',m)
 except AssertionError as e:
  if str(e).startswith('Compile current direct import first:'):
   with (E/'NMX_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(kind='blocked_dependency',attempt=a,module=m,reason=str(e)))+'\n')
   print(json.dumps(dict(attempt=a,module=m,status='not submitted',reason=str(e))),flush=True)
   continue
  raise
