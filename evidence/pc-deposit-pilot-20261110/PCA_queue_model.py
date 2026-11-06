from PCA_formal import run
for a,m in [(9,'PCA_State'),(10,'PCA_Event'),(11,'PCA_Owner'),(12,'PCA_Transcription'),(13,'PCA_CpiFrame')]:
 r=run(f'PCA_L{a:03d}','lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
