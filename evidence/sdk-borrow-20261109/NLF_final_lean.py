from NLF_formal import run
for i,m in [(76,'NLF_BorrowBounds'),(77,'NLF_SdkBorrowLaw')]:
 r=run(f'NLF_L{i:03d}','lean',m);assert r['exit_status']==0
