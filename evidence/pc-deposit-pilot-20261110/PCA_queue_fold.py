from PCA_formal import run
for a,m in [(41,'PCA_ProgramIds'),(42,'PCA_ValidatorReferences'),(43,'PCA_RowSpec_POOL_365'),(44,'PCA_RowSpec_POOL_364'),(45,'PCA_RowSpec_POOL_367'),(46,'PCA_ModeFold'),(47,'PCA_PageFold'),(48,'PCA_OwnerFold')]:
 r=run(f'PCA_L{a:03d}','lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
