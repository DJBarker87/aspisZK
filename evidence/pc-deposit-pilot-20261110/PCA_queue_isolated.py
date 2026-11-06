from PCA_formal import run
for a,m in [(52,'PCA_Layout'),(53,'PCA_GuardSteps'),(54,'PCA_FrameObstruction')]:
 r=run(f'PCA_L{a:03d}','lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
