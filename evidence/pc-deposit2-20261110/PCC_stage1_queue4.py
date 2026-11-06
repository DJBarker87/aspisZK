from PCC_formal import *
for a,m in [(22,'PCC_ErrorDecode'),(23,'PCC_DepositDecodeReference'),(24,'PCC_LaneReference'),(25,'PCC_PairValidation'),(26,'PCC_SingleOutputReference'),(27,'PCC_DecodeExtents'),(28,'PCC_LaneDomain'),(29,'PCC_ReferenceLaws'),(30,'PCC_ReferenceInvariant'),(31,'PCC_SharedInvariant'),(32,'PCC_CountClauses'),(33,'PCC_InfosClauses')]:
 r=run(f'PCC_L{a:03d}','lean',m)
 if r['exit_status']!=0:break
