from NMK_formal import *
for a,target in [('NMK_L006','NMK_RootWindow'),('NMK_L007','NMK_CompleteFold'),('NMK_L008','NMK_241Source')]:
 r=run(a,'lean',target)
 assert r['exit_status']==0,a
