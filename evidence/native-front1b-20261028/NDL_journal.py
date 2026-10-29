"""Compact attempt index; complete original receipts remain immutable."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
def entry(rc):
 a=rc['attempt'];data=(E/a/'receipt.json').read_bytes()
 out={k:rc.get(k) for k in ['attempt','kind','module','source_revision','source_tree_dirty','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','limits','cgroup']}
 out['deps_fingerprint_sha256']=hashlib.sha256(json.dumps(rc['deps_fingerprint'],sort_keys=True).encode()).hexdigest()
 out['receipt']=a+'/receipt.json';out['receipt_sha256']=hashlib.sha256(data).hexdigest()
 return out
if __name__=='__main__':
 p=E/'NDL_ATTEMPTS.jsonl';old=p.read_bytes();rows=[json.loads(l) for l in old.splitlines()]
 allrc=[json.loads((E/x['attempt']/'receipt.json').read_text()) for x in rows]
 full=''.join(json.dumps(rc)+'\n' for rc in allrc).encode()
 assert full==old,'initial conversion must preserve/reconstruct exact full journal'
 (E/'NDL_JOURNAL_FORMAT.json').write_text(json.dumps(dict(old_sha256=hashlib.sha256(old).hexdigest(),reconstruction='For each indexed receipt in order: json.dumps(json.loads(receipt.read_text())) plus newline; complete original receipts retained.',fields='Section6 target/exit/wall/RSS/swap/revision/axioms/source and dependency fingerprint plus exact receipt hash'),indent=2)+'\n')
 p.write_text(''.join(json.dumps(entry(rc))+'\n' for rc in allrc))
