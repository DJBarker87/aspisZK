"""Thread expanded entropy effects through exact callback and account entry."""
from pathlib import Path
import hashlib,json,sys
E=Path('evidence/pv-evh5-20261029')
mode=sys.argv[1]
if mode=='AccountFlow':
 src=Path('lean/PV_EVH_AccountCallback.lean');s=src.read_text()
 s=s.replace('import PV_EVH_EntropyGenerate','import PV_EVH_EntropyFlow\nimport PV_EVH_AccountCallback')
 s=s.replace('namespace PV_EVH_AccountCallback','namespace PV_EVH_AccountFlow').replace('end PV_EVH_AccountCallback','end PV_EVH_AccountFlow')
 s=s.replace('open PV_EVH_EntropyGenerate (Secrets)','open PV_EVH_EntropyFlow (Secrets)')
 s=s.replace('(fuel : Nat) (answers : EntropyAnswers)', '(fuel : Nat) (answers : EntropyAnswers)\n    (entropy : PV_EVH_EntropyStep.Callees) (nonzero_OPEN : Array U8 32#usize → P Bool)')
 s=s.replace('PV_EVH_EntropyGenerate.generate fuel answers a','PV_EVH_EntropyFlow.generate fuel answers entropy nonzero_OPEN a')
 s=s.replace('callMut inst fuel answers account_OPEN','callMut inst fuel answers entropy nonzero_OPEN account_OPEN')
 s=s.replace('next inst fuel answers account_OPEN','next inst fuel answers entropy nonzero_OPEN account_OPEN')
 s=s.replace('    (same :', '    (he : PV_EVH_EntropyStep.Compatible entropy)\n    (hn : ∀ n, FinishedView (nonzero_OPEN n) (aspis_prover.state_only_entropy.entropy_nonzero32 n))\n    (same :')
 s=s.replace('PV_EVH_EntropyGenerate.generate_fixed fuel answers same a','PV_EVH_EntropyFlow.generate_fixed fuel answers entropy he same nonzero_OPEN hn a')
 s=s.replace('callMut_fixed inst fuel answers account_OPEN same','callMut_fixed inst fuel answers entropy nonzero_OPEN account_OPEN he hn same')
else:
 assert mode=='AccountFlowEntry'
 src=Path('lean/PV_EVH_AccountGuard.lean');s=src.read_text().replace('import PV_EVH_AccountCallback','import PV_EVH_AccountFlow')
 s=s.replace('PV_EVH_AccountGuard','PV_EVH_AccountFlowEntry').replace('PV_EVH_AccountCallback','PV_EVH_AccountFlow')
 s=s.replace('(retryFuel entropyFuel : Nat) (answers : EntropyAnswers)', '(retryFuel entropyFuel : Nat) (answers : EntropyAnswers)\n    (entropy : PV_EVH_EntropyStep.Callees) (nonzero_OPEN : Array U8 32#usize → P Bool)')
 s=s.replace('retrying inst retryFuel entropyFuel answers public1','retrying inst retryFuel entropyFuel answers entropy nonzero_OPEN public1')
 s=s.replace('entry inst retryFuel entropyFuel answers public1','entry inst retryFuel entropyFuel answers entropy nonzero_OPEN public1')
 s=s.replace('PV_EVH_AccountFlow.next inst entropyFuel answers account_OPEN','PV_EVH_AccountFlow.next inst entropyFuel answers entropy nonzero_OPEN account_OPEN')
 s=s.replace('    (guard_fixed :', '    (he : PV_EVH_EntropyStep.Compatible entropy)\n    (hn : ∀ n, FinishedView (nonzero_OPEN n) (aspis_prover.state_only_entropy.entropy_nonzero32 n))\n    (guard_fixed :')
 s=s.replace('PV_EVH_AccountFlow.next_fixed inst entropyFuel answers account_OPEN same','PV_EVH_AccountFlow.next_fixed inst entropyFuel answers entropy nonzero_OPEN account_OPEN he hn same')
 s=s.replace('retrying_fixed inst retryFuel entropyFuel answers public1','retrying_fixed inst retryFuel entropyFuel answers entropy nonzero_OPEN public1')
 s=s.replace('prove_OPEN guard_OPEN guard_fixed same','prove_OPEN guard_OPEN he hn guard_fixed same')
p=Path('lean/PV_EVH_'+mode+'.lean');r=E/(mode+'-generation.json')
record=json.dumps(dict(input=str(src),input_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(s.encode()).hexdigest(),scope='local Result transport with source-directed open entropy leaves; not full native coverage'),indent=2)+'\n'
if '--check' in sys.argv:assert p.read_text()==s and r.read_text()==record;print('PASS entropy entry generation',mode)
else:p.write_text(s);r.write_text(record)
