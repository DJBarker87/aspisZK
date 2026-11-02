"""Collect public receipts/digests only; never download private proof/key corpus."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-uc-20261029';H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-uc-20261029/'
files=['final-gates/ready/build.json']
roots=['main','decode_wallet_record','walletPath_same_public','stdout_recomputable','pubkey_recomputable','extracted_fd_formatter_public','extracted_json_formatter_recomputable','extracted_pubkey_formatter_recomputable']
files += ['final-gates/d561/axioms/'+n+'_REACHABLE.txt' for n in roots]
for name in files:
 p=E/name;p.parent.mkdir(parents=True,exist_ok=True)
 subprocess.run(['scp',H+':'+D+name,str(p)],check=True)
 Path(str(p)+'.sha256').write_text(hashlib.sha256(p.read_bytes()).hexdigest()+'\n')
# Finite emitted-Lean vectors: compare complete output with the frozen native
# decoder expectation table, not with a new or weakened comparator.
p=E/'lean75038';r=json.loads((p/'receipt.json').read_text());assert r['exit']==0
import re
lines=[x for x in (p/'output.log').read_text().splitlines() if re.fullmatch(r'[0-9]+(?:,[0-9]+)+',x)]
expect=json.loads((E/'decoder-execution-expectations.json').read_text());assert len(lines)==len(expect['rows'])==3
rows=[]
for line,want in zip(lines,expect['rows']):
 values=list(map(int,line.split(',')));assert values==want['expected'],want['label']
 rows.append(dict(label=want['label'],values=len(values),identical=True,csv_sha256=hashlib.sha256((line+'\n').encode()).hexdigest()))
(E/'final-gates/d561/decoder-execution.json').write_text(json.dumps(dict(status='PASS finite emitted-model/native expectation comparison',receipt='lean75038/receipt.json',rows=rows,expected_sha256=hashlib.sha256((E/'decoder-execution-expectations.json').read_bytes()).hexdigest(),scope='Three 212-byte public patterns (zero, ff, ramp); not a universal theorem or new whole-client CT measurement. Historical native output checker N75140 and unchanged decoder shape reused.'),indent=2)+'\n')
print(json.dumps(dict(collected=len(files),decoder_vectors='3/3 match')))
