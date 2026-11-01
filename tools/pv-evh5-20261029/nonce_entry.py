"""Thread the expanded nonce source spines through the accepted entry graph."""
from pathlib import Path
import hashlib,json,sys
mode=sys.argv[1];assert mode in ['NonceWithAttempt','NonceProver']
extra=' (fallibleCallees : PV_EVH_NonceReserveFallible.Callees) (pathCallees : PV_EVH_NoncePath.Callees) (nonceCallees : PV_EVH_NonceReserve.Callees)'
views=' (fallible_same : PV_EVH_NonceReserveFallible.Compatible fallibleCallees) (path_same : PV_EVH_NoncePath.Compatible pathCallees) (nonce_same : PV_EVH_NonceReserve.Compatible nonceCallees)'
if mode=='NonceWithAttempt':
 src=Path('lean/PV_EVH_DurableWithAttempt.lean');s=src.read_text().replace('PV_EVH_DurableWithAttempt','PV_EVH_NonceWithAttempt').replace('PV_EVH_DurableReserveBuild','PV_EVH_NonceReserveBuild')
 s=s.replace('(fileAnswers : PV_EVH_NonceWorld.Answers)', '(fileAnswers : PV_EVH_NonceWorld.Answers)'+extra)
 s=s.replace('fileAnswers reserveCallees','fileAnswers fallibleCallees pathCallees nonceCallees reserveCallees')
 s=s.replace('(reserve_same : PV_EVH_NonceReserveBuild.Compatible reserveCallees)', '(reserve_same : PV_EVH_NonceReserveBuild.Compatible reserveCallees)'+views)
 s=s.replace('reserve_same files_same','reserve_same files_same fallible_same path_same nonce_same')
else:
 src=Path('lean/PV_EVH_DurableFlow.lean');s=src.read_text().replace('PV_EVH_DurableFlow','PV_EVH_NonceProver').replace('PV_EVH_DurableWithAttempt','PV_EVH_NonceWithAttempt').replace('PV_EVH_DurableReserveBuild','PV_EVH_NonceReserveBuild')
 s=s.replace('(files : PV_EVH_NonceWorld.Answers)', '(files : PV_EVH_NonceWorld.Answers)'+extra)
 s=s.replace('(hf : PV_EVH_NonceWorld.Compatible files)', '(hf : PV_EVH_NonceWorld.Compatible files)'+views)
 s=s.replace('maskedCallees h b r files public1','maskedCallees h b r files fallibleCallees pathCallees nonceCallees public1')
 s=s.replace('maskedCallees_fixed h b r files public1','maskedCallees_fixed h b r files fallibleCallees pathCallees nonceCallees public1')
 s=s.replace('files r b','files fallibleCallees pathCallees nonceCallees r b')
 s=s.replace('r b hb hf hr','r b hb hf hr fallible_same path_same nonce_same')
 s=s.replace('h b r files guard_OPEN','h b r files fallibleCallees pathCallees nonceCallees guard_OPEN')
 s=s.replace('hash hh hb hr hf)', 'hash hh hb hr hf fallible_same path_same nonce_same)')
p=Path('lean/PV_EVH_'+mode+'.lean');r=Path('evidence/pv-evh5-20261029/'+mode+'-generation.json')
record=json.dumps(dict(input=str(src),input_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(s.encode()).hexdigest(),scope='source Result transport only; native hash, formatting, allocation/runtime and remaining callees OPEN'),indent=2)+'\n'
if '--check' in sys.argv:assert p.read_text()==s and r.read_text()==record;print('PASS nonce entry generation',mode)
else:p.write_text(s);r.write_text(record)
