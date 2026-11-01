"""Replace inherited Result-only nonce helpers by their source Prefix spines."""
from pathlib import Path
import hashlib,json,sys
src=Path('lean/PV_EVH_DurableReserveBuild.lean');s=src.read_text()
s=s.replace('PV_EVH_NonceSource','PV_EVH_NonceReserve').replace('PV_EVH_DurableReserveBuild','PV_EVH_NonceReserveBuild')
extra=' (fallibleCallees : PV_EVH_NonceReserveFallible.Callees) (pathCallees : PV_EVH_NoncePath.Callees) (nonceCallees : PV_EVH_NonceReserve.Callees)'
s=s.replace(' (c : Callees)',extra+' (c : Callees)')
s=s.replace('structure Compatible'+extra+' (c : Callees)','structure Compatible (c : Callees)')
s=s.replace(' (files_same : PV_EVH_NonceWorld.Compatible fileAnswers)', ' (files_same : PV_EVH_NonceWorld.Compatible fileAnswers) (fallible_same : PV_EVH_NonceReserveFallible.Compatible fallibleCallees) (path_same : PV_EVH_NoncePath.Compatible pathCallees) (nonce_same : PV_EVH_NonceReserve.Compatible nonceCallees)')
s=s.replace('PV_EVH_Prefix.ofM (PV_EVH_NonceReserve.reserve fileAnswers nonce_store context.statement_digest context.mask_nonce)', 'PV_EVH_NonceReserve.run nonce_store context.statement_digest context.mask_nonce fileAnswers fallibleCallees pathCallees nonceCallees')
s=s.replace('nonce_store fileAnswers c)', 'nonce_store fileAnswers fallibleCallees pathCallees nonceCallees c)')
s=s.replace('PV_EVH_Prefix.ofM_fixed _ _ (PV_EVH_NonceReserve.reserve_fixed fileAnswers files_same _ _ _)', 'PV_EVH_NonceReserve.run_fixed _ _ _ fileAnswers fallibleCallees pathCallees nonceCallees nonce_same files_same fallible_same path_same')
p=Path('lean/PV_EVH_NonceReserveBuild.lean');r=Path('evidence/pv-evh5-20261029/nonce-build-generation.json')
record=json.dumps(dict(input=str(src),input_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(s.encode()).hexdigest(),scope='source-spine expansion only; path hash/allocation/error helpers remain OPEN'),indent=2)+'\n'
if '--check' in sys.argv:assert p.read_text()==s and r.read_text()==record;print('PASS nonce build generation')
else:p.write_text(s);r.write_text(record)
