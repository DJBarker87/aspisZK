from run import H
import subprocess,time,json,sys
for who in ['control','candidate']:
 for attempt in range(1,11):
  if who=='control' and attempt==1:
   # Initial admission refusal at 13:15:41 UTC; required three-minute interval.
   time.sleep(max(0,1793106941.31+180-time.time()))
  result=subprocess.run(['python3',str(H/'run.py'),who,str(attempt)])
  if result.returncode==0:break
  p=H/f'build-{who}-{attempt}'
  reservation=json.loads((p/'reservation.json').read_text())
  if reservation.get('error'):
   sys.exit('reservation infrastructure error: '+reservation['error'])
  if result.returncode!=78:sys.exit(result.returncode)
  if attempt==10:sys.exit(78)
  time.sleep(180)
 else:sys.exit(78)
