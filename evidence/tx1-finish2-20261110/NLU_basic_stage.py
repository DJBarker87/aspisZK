from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
modules=['NLU_InspectStubs','NLU_Words','NLU_Cell','NLU_HighCut','NLU_HighLoop','NLU_TerminalTransport','NLU_InputDomain','NLU_Next','NLU_Invariant','NLU_Nested','NLU_CanonicalTransport','NLU_TerminalCanonical','NLU_ClaimsCanonical','NLU_SameTerminal','NLU_SlotFrame']+['NLU_SlotFrame'+str(i) for i in range(5)]+['NLU_SlotFrames','NLU_Verified','NLU_FieldLog','NLU_GeneratedMul','NLU_FieldValues','NLU_Arithmetic','NLU_ConstructCut','NLU_ConstructArrays','NLU_ConstructMisc','NLU_ConstructChallenges','NLU_ConstructPoints','NLU_ConstructTranscript','NLU_ConstructComplete','NLU_Frontier','NLU_FrontierSource']
for module in modules:
 source=E/'NLU_generated'/(module+'.lean');ok=False
 for p in E.glob('NLU_L*/receipt.json'):
  x=json.loads(p.read_text());snap=p.parent/'sources/NLU_generated'/(module+'.lean')
  if x.get('module')==module and x['exit_status']==0 and snap.exists() and snap.read_bytes()==source.read_bytes():ok=True
 if ok:continue
 used={int(p.parent.name[-3:]) for p in E.glob('NLU_L*/receipt.json')}
 n=next(i for i in range(57,111) if i not in used and i!=60);a=f'NLU_L{n:03}'
 subprocess.run([sys.executable,str(E/'NLU_config.py'),a,module],check=True)
 if subprocess.run([sys.executable,str(E/'NLU_run.py'),a]).returncode:sys.exit(1)
