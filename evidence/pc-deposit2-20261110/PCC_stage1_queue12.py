from PCC_formal import *
for a,m in [(60, 'PCC_SingleCanonical'), (61, 'PCC_CpiMetaExclusion'), (62, 'PCC_ModeBounds'), (63, 'PCC_SingleFrame')]:
 r=run(f"PCC_L{a:03d}","lean",m)
 if r["exit_status"]!=0:break
