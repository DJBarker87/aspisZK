from PCA_formal import run
for a,m in [(47,'PCA_Owner'),(48,'PCA_Transcription'),(49,'PCA_Borrow'),(50,'PCA_ModeFold'),(51,'PCA_PageFold'),(52,'PCA_OwnerFold')]:
 r=run(f'PCA_L{a:03d}','lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
