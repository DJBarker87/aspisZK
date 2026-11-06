from PCC_formal import *
for a,m in [(44, 'PCC_SharedGuardFrame'), (45, 'PCC_ReferenceAssoc'), (46, 'PCC_PureFrames'), (47, 'PCC_DecodeFrame'), (48, 'PCC_LiveTokenInvariant'), (49, 'PCC_NativeLinkage'), (50, 'PCC_FreshReject'), (51, 'PCC_ZeroedReject'), (52, 'PCC_ErrorNoninjective')]:
 r=run(f"PCC_L{a:03d}","lean",m)
 if r["exit_status"]!=0:break
