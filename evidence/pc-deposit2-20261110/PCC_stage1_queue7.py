from PCC_formal import *
for a,m in [(36, 'PCC_InfosClauses'), (37, 'PCC_PageImage'), (38, 'PCC_PageReference'), (39, 'PCC_PageExtents'), (40, 'PCC_PageFrame'), (41, 'PCC_UniqueLoop'), (42, 'PCC_SharedFailure'), (43, 'PCC_SharedGuardFrame'), (44, 'PCC_ReferenceAssoc'), (45, 'PCC_PureFrames'), (46, 'PCC_DecodeFrame'), (47, 'PCC_LiveTokenInvariant'), (48, 'PCC_NativeLinkage'), (49, 'PCC_FreshReject'), (50, 'PCC_ZeroedReject'), (51, 'PCC_ErrorNoninjective')]:
 r=run(f"PCC_L{a:03d}","lean",m)
 if r["exit_status"]!=0:break
