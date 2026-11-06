from PCC_formal import *
for a,m in [(53, 'PCC_ZeroedReject'), (54, 'PCC_ErrorNoninjective'), (55, 'PCC_ExclusiveReference'), (56, 'PCC_ExclusiveInvariant'), (57, 'PCC_ExitCleanup'), (58, 'PCC_SingleCanonical'), (59, 'PCC_CpiMetaExclusion'), (60, 'PCC_ModeBounds'), (61, 'PCC_SingleFrame')]:
 r=run(f"PCC_L{a:03d}","lean",m)
 if r["exit_status"]!=0:break
