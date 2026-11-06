from PCC_formal import *
for a,m in [(45, 'PCC_SharedGuardFrame'), (46, 'PCC_ReferenceAssoc'), (47, 'PCC_PureFrames'), (48, 'PCC_DecodeFrame'), (49, 'PCC_LiveTokenInvariant'), (50, 'PCC_NativeLinkage'), (51, 'PCC_FreshReject'), (52, 'PCC_ZeroedReject'), (53, 'PCC_ErrorNoninjective'), (54, 'PCC_ExclusiveReference'), (55, 'PCC_ExclusiveInvariant'), (56, 'PCC_ExitCleanup'), (57, 'PCC_SingleCanonical'), (58, 'PCC_CpiMetaExclusion'), (59, 'PCC_ModeBounds'), (60, 'PCC_SingleFrame')]:
 r=run(f"PCC_L{a:03d}","lean",m)
 if r["exit_status"]!=0:break
