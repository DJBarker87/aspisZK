from NLF_formal import run
for i,m in [(84,'NLF_StatementReview'),(85,'NLF_ConsumerReview')]:
 r=run(f'NLF_L{i:03d}','lean',m);assert r['exit_status']==0
