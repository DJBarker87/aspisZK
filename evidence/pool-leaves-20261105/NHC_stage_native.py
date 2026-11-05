from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,target in [('NHC_L050','batch1'),('NHC_L051','scan')]:
 r=subprocess.run([sys.executable,str(E/'NHC_run.py'),a,'audit',target],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,target,r.returncode,flush=True)
 if r.returncode:print((r.stdout+r.stderr)[-1000:]);sys.exit(r.returncode)
r=subprocess.run([sys.executable,str(E/'NHC_request_campaign.py')]);sys.exit(r.returncode)
