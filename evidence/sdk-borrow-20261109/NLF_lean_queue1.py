from NLF_formal import run
for i,m in [(19,'NLF_ReleaseInvariant'),(20,'NLF_RuntimeInterpretation'),(21,'NLF_ViewLaws')]:
 r=run(f'NLF_L{i:03d}','lean',m)
 if r['exit_status']:break
