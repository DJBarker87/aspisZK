from pathlib import Path
import json,subprocess,sys,hashlib
E=Path(__file__).resolve().parent
plan=[(21,'NMO_BlindStored',['NMO_ArrayStored']),(22,'NMO_ArrayReachable',['NMO_BlindStored']),(23,'NMO_MaskAtState',['NMO_ArrayReachable']),(24,'NMO_MaskValue',['NMO_MaskAtState']),(25,'NMO_MaskStored',['NMO_MaskValue']),(33,'NMO_ExtraValue',['NMO_ClaimsAtState']),(27,'NMO_ExtraStored',['NMO_ExtraValue']),(28,'NMO_ExtraCell',['NMO_ExtraStored']),(29,'NMO_ArithmeticValue',[]),(30,'NMO_ArithmeticAtState',['NMO_ArithmeticValue','NMO_MaskStored','NMO_MulAtState','NMO_ExtraStored']),(36,'NMO_ErrorFrontier',['NMO_PrefixErrors']),(37,'NMO_TerminalWindows',[]),(38,'NMO_ChallengeWindows',['NMO_TerminalWindows'])]
def green(m):
 s=E/(m+'.lean')
 return any((x:=json.loads(p.read_text())).get('module')==m and x.get('kind')=='lean'and x['exit_status']==0 and (snap:=p.parent/'sources'/(m+'.lean')).exists()and snap.read_bytes()==s.read_bytes()for p in E.glob('NMO_L*/receipt.json'))
for n,m,deps in plan:
 if (E/'NMO_STOP_AFTER_SCOPE').exists():break
 if green(m):continue
 if any(not green(d)for d in deps):print(json.dumps(dict(module=m,status='pending dependency')),flush=True);continue
 a=f'NMO_L{n:03}';subprocess.run([sys.executable,str(E/'NMO_config.py'),a,m],check=True);subprocess.run([sys.executable,str(E/'NMO_run.py'),a])
 assert(E/a/'receipt.json').exists(),'Recover read-only; no new launch'
 if not green(m):print(json.dumps(dict(module=m,status='not green; independent targets continue')),flush=True)
