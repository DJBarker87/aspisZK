from pathlib import Path
import hashlib,json
base=Path('tools/pv-runjoin-20261026/concrete-attempt/native-fault')
base.mkdir(exist_ok=True)
p=Path('crates/aspis-prover/src/state_only_entropy.rs')
s=p.read_text()
def item(start):
    i=s.index(start);j=s.index('{',i);depth=1;k=j+1
    while depth:
        if s[k]=='{':depth+=1
        elif s[k]=='}':depth-=1
        k+=1
    return s[i:k],i,k
items=[item('pub enum StateOnlyAttemptEntropyError'),item('impl From<getrandom::Error>'),item('pub struct StateOnlyAttemptSecrets'),item('fn entropy_nonzero32'),item('pub fn generate_for_mask_nonce(')]
selected='use zeroize::Zeroizing;\nconst ENTROPY_RETRY_LIMIT:usize=16;\n'
selected+=items[0][0]+'\n'+items[1][0]+'\n'+items[2][0]+'\n'+items[3][0]+'\nimpl StateOnlyAttemptSecrets {\n'+items[4][0]+'\n}\n'
(base/'selected.rs').write_text(selected)
rows=[dict(start_byte=i,end_byte=j,sha256=hashlib.sha256(v.encode()).hexdigest()) for v,i,j in items]
Path('evidence/pv-runjoin-20261026/concrete-attempt/native-fault-source.json').write_text(json.dumps(dict(source=str(p),source_sha256=hashlib.sha256(s.encode()).hexdigest(),selected_sha256=hashlib.sha256(selected.encode()).hexdigest(),items=rows,modifications='only selection, use and unchanged retry-limit declaration; literal method/error/helper bodies'),indent=2)+'\n')
