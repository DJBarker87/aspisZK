"""Exact frozen slot reference and admitted native receipt checks; no status promotion."""
from pathlib import Path
import re,subprocess,json,hashlib,copy
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
source=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/compact.rs'],text=True)
ref=(E/'NGD_references.rs.txt').read_text()
def body(s):
 start=s.index('pub const fn slot_offset');end=s.index('\n}',start)+2 if '\n}' in s[start:] else len(s)
 # Balanced braces rather than line formatting determines the exact body.
 a=s.index('{',start);depth=1;i=a+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|\S',s[start:i])
def valid(r):return body(source)==body(r) and re.search(r'SLOT_NODES\s*:\s*\[usize;\s*6\]\s*=\s*\[146,\s*146,\s*128,\s*172,\s*172,\s*150\]',r) is not None
assert valid(ref)
assert not valid(ref.replace('i+=1','i+=2'))
assert not valid(ref.replace('[146,146,128,172,172,150]','[145,146,128,172,172,150]'))
rows=[]
for i,expected in [(1,0),(2,1),(3,0),(4,1),(7,0),(8,1)]:
 a=f'NGD_K{i:03}';r=json.loads((E/a/'receipt.json').read_text());ad=json.loads((E/(a+'-admission.json')).read_text())
 assert r['exit_status']==expected and ad['exit']==0 and ad['reservation']['allowed'] is True
 assert json.loads((E/(a+'-graph-check.json')).read_text())['graph_matches_frozen']
 assert json.loads((E/(a+'-lock-check.json')).read_text())['unchanged']
 assert not json.loads((E/(a+'-source-check.json')).read_text())['errors']
 log=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED'if expected else'SUCCESSFUL') in log
 if expected:assert re.search(r'\*\* 1 of \d+ failed',log)
 rows.append(dict(attempt=a,receipt_sha256=hashlib.sha256((E/a/'receipt.json').read_bytes()).hexdigest()))
(E/'NGD_SLOT_CHECK.json').write_text(json.dumps(dict(status='PASS',frozen_revision=F,source_function_tokens_identical=True,mutations_rejected=2,native=rows,scope='slot_all executes ACTUAL frozen function; slot_native_step is arithmetic support only, never an independent actual-body bridge'),indent=2)+'\n')
