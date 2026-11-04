"""Frozen request/reference association. No source mutation or model selection."""
from pathlib import Path
import subprocess,re,hashlib,json
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
P='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
def frozen_body(text,name):
 a=text.index('pub fn '+name+'(');return text[a:text.index('\n}',a)+2]
def request_reference(source=None):
 text=source if source is not None else subprocess.check_output(['git','show',REV+':'+P],text=True)
 n='decode_pool_v1_pair_forest_terminal_request_v1';ref='decode_pool_v1_pair_forest_terminal_request_reference_v1'
 actual=frozen_body(text,n);reference=frozen_body(text,ref)
 normalized=reference.replace('pub fn '+ref+'(','pub fn '+n+'(').replace('bytes: &[u8; POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES]','bytes: &[u8]').replace('.map_err(|e| PoolV1PairForestTerminalFormatErrorV1::Payment(e))','.map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)')
 assert actual==normalized,'frozen request/reference source mismatch'
 assert actual.count('decode_pool_v1_private_transfer_public_v1(')==1 and actual.count('decode_pool_v1_withdrawal_public_v1(')==1
 return dict(frozen_revision=REV,native_body_sha256=hashlib.sha256(actual.encode()).hexdigest(),reference_body_sha256=hashlib.sha256(reference.encode()).hexdigest(),exact_normalized_source=True,normalizations=['signature Slice versus fixed320-byte array','Payment constructor versus explicit lambda; both execute identical pure enum constructor'],same_child_calls=True,same_error_order=True,same_output_fields=True)
if __name__=='__main__':print(json.dumps(request_reference(),indent=1))
