from NMD_formal import *
import subprocess
r=subprocess.run([sys.executable,str(E/'NMD_program_queue.py'),'58']);assert r.returncode==0
for i,m in enumerate(['NMD_CutState','NMD_SegmentFold','NMD_CandidateFold'],1):
 r=run(f'NMD_L{i:03}','lean',m)
 if r['exit_status']:break
r=run('NMD_L004','inspect','newest-kani-bundle',['python3','NMD_newest_download.py'],{'NMD_newest_download.py':(E/'NMD_newest_download.py').read_text()})
