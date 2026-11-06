from PCC_formal import *
for a,m in [(34, 'PCC_CountClauses'), (35, 'PCC_InfosClauses'), (36, 'PCC_PageImage'), (37, 'PCC_PageReference'), (38, 'PCC_PageExtents'), (39, 'PCC_PageFrame'), (40, 'PCC_UniqueLoop'), (41, 'PCC_SharedFailure'), (42, 'PCC_SharedGuardFrame'), (43, 'PCC_ReferenceAssoc'), (44, 'PCC_PureFrames'), (45, 'PCC_DecodeFrame'), (46, 'PCC_LiveTokenInvariant'), (47, 'PCC_NativeLinkage'), (48, 'PCC_FreshReject'), (49, 'PCC_ZeroedReject'), (50, 'PCC_ErrorNoninjective')]:
 r=run(f"PCC_L{a:03d}","lean",m)
 if r["exit_status"]!=0:break
