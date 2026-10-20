import base64,hashlib,json,pathlib,subprocess,sys
from r1_devnet_rpc import rpc
c=json.load(open(sys.argv[1]));out=pathlib.Path(sys.argv[2]);out.mkdir(exist_ok=False)
cli=str(pathlib.Path.home()/'.local/share/solana/install/active_release/bin/solana-keygen')
buffer=subprocess.check_output([cli,'pubkey','keys/verifier-deploy-buffer.json'],text=True).strip()
a=rpc(c['rpc_url'],'getAccountInfo',[buffer,{'encoding':'base64','commitment':'finalized'}]);v=a['value'];d=base64.b64decode(v['data'][0]);elf=pathlib.Path(c['artifacts']['verifier']).read_bytes()
summary={'buffer':buffer,'slot':a['context']['slot'],'lamports':v['lamports'],'owner':v['owner'],'bytes':len(d),'header_hex':d[:37].hex(),'elf_bytes':len(elf),'body_sha256':hashlib.sha256(d[37:]).hexdigest(),'matching_bytes':sum(x==y for x,y in zip(d[37:],elf)),'mismatching_900byte_chunks':[i for i in range(0,len(elf),900) if d[37+i:37+i+900]!=elf[i:i+900]]}
(out/'buffer.json').write_text(json.dumps(summary,indent=2))
sigs=rpc(c['rpc_url'],'getSignaturesForAddress',[buffer,{'limit':10,'commitment':'finalized'}]);(out/'signatures.json').write_text(json.dumps(sigs,indent=2))
print(json.dumps({**summary,'mismatching_900byte_chunks':len(summary['mismatching_900byte_chunks']),'recent_signatures':sigs},indent=2))
