import os,time,subprocess,sys
while True:
 try: os.kill(44025,0)
 except ProcessLookupError: break
 time.sleep(10)
from NMB_formal import run
for a,m in [(55,"NMB_StorageDomains"),(56,"NMB_Cleanup"),(57,"NMB_CleanupAdmitted"),(58,"NMB_ArrayFrame"),(59,"NMB_RowSpec094"),(60,"NMB_TypedTrace"),(61,"NMB_TypedControl"),(62,"NMB_OwnedTyped")]:
 r=run(f"NMB_L{a:03d}","lean",m)
 if r["exit_status"]:sys.exit(r["exit_status"])
