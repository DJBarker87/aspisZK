from PCC_formal import *
for a,m in [(32, 'PCC_SharedInvariant'), (33, 'PCC_CountClauses'), (34, 'PCC_InfosClauses'), (35, 'PCC_PageImage'), (36, 'PCC_PageReference'), (37, 'PCC_PageExtents'), (38, 'PCC_PageFrame'), (39, 'PCC_UniqueLoop'), (40, 'PCC_SharedFailure'), (41, 'PCC_SharedGuardFrame'), (42, 'PCC_ReferenceAssoc'), (43, 'PCC_PureFrames'), (44, 'PCC_DecodeFrame')]:
 r=run(f"PCC_L{a:03d}","lean",m)
 if r["exit_status"]!=0:break
