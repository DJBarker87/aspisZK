from run import H
import subprocess,time,json,sys,datetime
# Reservation changed between outside preflight and inside barrier; wait 3 min.
time.sleep(max(0,datetime.datetime.fromisoformat('2026-10-27T13:19:15.705565+00:00').timestamp()+180-time.time()))
for who in ['control','candidate']:
 for attempt in range(2,12):
  result=subprocess.run(['python3',str(H/'run.py'),who,str(attempt)])
  if result.returncode==0:break
  p=H/f'build-{who}-{attempt}'
  reservation=json.loads((p/'barrier.json' if (p/'barrier.json').exists() else p/'reservation.json').read_text())
  if reservation.get('error'):sys.exit('reservation infrastructure error: '+reservation['error'])
  if result.returncode!=78:sys.exit(result.returncode)
  if attempt==11:sys.exit(78)
  time.sleep(180)
 else:sys.exit(78)
