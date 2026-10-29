"""Check admitted mask/preweighted domains against frozen source call sites."""
from pathlib import Path
import re,json,hashlib,subprocess
O=Path('evidence/pv-b3p6-20261028/resume16');P=Path('tools/pv-b3p6-20261028/v244')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
maskset={1749,2048,2049,4097,6144,6145,26214};maskrows=[]
for src,constants in [(Path('crates/aspis-r1-cost-probe/src/host_copy_terminal.rs'),Path('crates/aspis-r1-cost-probe/src/host_copy_terminal_constants.rs')),(Path('crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'),Path('crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs'))]:
 text=src.read_text();a=text.index('fn selector_mask_sum_16(');b=text.index('\n#[derive',a);body=text[a:b]
 sites=[(i,l.strip())for i,l in enumerate(text.splitlines(),1)if re.search(r'\bselector_mask_sum_16\s*\(',l) and not l.strip().startswith('fn ')]
 assert len(sites)==1,sites
 start=text.index('fn active_literal(');end=text.index('\n    #[',start);caller=text[start:end]
 assert 'let mask = constants::ACTIVE_ROW_MASKS[block];'in caller and 'if mask != 0 {'in caller and 'while block < 64 {'in caller
 table=re.search(r'const ACTIVE_ROW_MASKS: \[u16; 64\] = \[([^]]+)\]',constants.read_text());values=list(map(int,table[1].split(',')));assert len(values)==64 and set(values)<=maskset
 maskrows.append(dict(source=str(src),sha256=sha(src),function_sha256=hashlib.sha256(body.encode()).hexdigest(),callsites=[dict(line=i,text=l)for i,l in sites],caller_body=caller,constants=str(constants),constants_sha256=sha(constants),table=values,check='all 64 table cells are in the 7-mask domain; the only caller indexes 0..64 and tests nonzero'))
# Token identity checks the two separately deployed bodies, not a shared source assumption.
tok=lambda s:re.findall(r'\w+|[^\s]',re.sub(r'//[^\n]*','',s))
assert tok(maskrows[0]['caller_body'])==tok(maskrows[1]['caller_body'])
src=Path('crates/aspis-r1-cost-probe/src/host_terminal.rs');text=src.read_text()
callpat=re.compile(r'\badd_preweighted(?:_shared_selector)?\s*\(')
calls=[]
for m in callpat.finditer(text):
 prefix=text[max(0,m.start()-4):m.start()]
 if 'fn 'in prefix:continue
 depth=1;i=m.end()
 while depth:
  depth+=(text[i]=='(')-(text[i]==')');i+=1
 calls.append(dict(line=text[:m.start()].count('\n')+1,text=text[m.start():i]))
assert len(calls)==9,calls
shapes=[(16,0,'initial'),(16,16,'absorption'),(17,32,'path'),(33,49,'range'),(33,49,'range/shared'),(2,82,'conservation'),(12,0,'occupancy'),(8,84,'public_digest_lanes'),(2,92,'scalars')]
for c,(n,start,name) in zip(calls,shapes):
 assert re.search(r',\s*'+str(start)+r'\s*,',c['text']),c
 c.update(N=n,start=start,value=name,domain_proof=dict(nonempty=n>0,end=start+n,last_group=(start+n-1)//4,all_stores_bounded=(start+n-1)//4<24))
(O/'DOMAINS.json').write_text(json.dumps(dict(mask=maskrows,preweighted=dict(source=str(src),sha256=sha(src),callsites=calls,shape_authority='resume15 preweighted actual caller shape Lean laws; array declarations checked in frozen source',status='static source/domain check; no reachability pruning; full symbolic field values required'),all_crates_grep=subprocess.run(['rg','-n',r'\b(selector_mask_sum_16|add_preweighted|add_preweighted_shared_selector)\s*\(','crates/'],capture_output=True,text=True).stdout.splitlines()),indent=2)+'\n')
print('domains: both mask callers, 128 table cells, 9 preweighted call sites checked')
