from NMX_formal import *
jobs=[('NMX_L078','NMX_S016'),('NMX_L079','NMX_CanonicalTarget'),('NMX_L080','NMX_RSL233Replay'),('NMX_L081','NMX_LeafInstall'),('NMX_L082','NMX_ErrorCloneCut')]
for a,m in jobs:
 r=run(a,'lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
