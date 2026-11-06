from PCC_formal import *
for a,m in [(58, 'PCC_ExitCleanup'), (59, 'PCC_SingleCanonical'), (60, 'PCC_CpiMetaExclusion'), (61, 'PCC_ModeBounds'), (62, 'PCC_SingleFrame')]:
 r=run(f"PCC_L{a:03d}","lean",m)
 if r["exit_status"]!=0:break
