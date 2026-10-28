import subprocess,json,pathlib,re,collections
E=pathlib.Path(__file__).resolve().parent
C=pathlib.Path('/private/tmp/pv-kscan-cache-20261028');C.mkdir(exist_ok=True)
heads=json.loads((E/'heads.json').read_text())
class Git:
 def __init__(self): self.p=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 def get(self,key):
  self.p.stdin.write((key+'\n').encode());self.p.stdin.flush();h=self.p.stdout.readline().decode().strip().split()
  if h[-1]=='missing':return b''
  b=self.p.stdout.read(int(h[-1]));self.p.stdout.read(1);return b
G=Git(); entries={}; trees={}
for ref,h in heads.items():
 tree={line.split('\t')[1]:line.split()[2] for line in subprocess.check_output(['git','ls-tree','-r',h],text=True).splitlines()};trees[ref]=tree
 for p,b in tree.items():
  if p.startswith('evidence/') and (p.startswith('evidence/pv-') or any(x in p.split('/')[1] for x in ['p6','batch-effects','privacy-recount'])):
   entries.setdefault((p,b),[]).append(ref)
(C/'tree-index.json').write_text(json.dumps({r:{p:b for p,b in t.items() if p.startswith('evidence/')} for r,t in trees.items()}))
receipts=[]; logs=[]; docs=[]
for (p,b),refs in entries.items():
 if not (p.endswith('.json') or p.endswith('.jsonl') or p.endswith('.md') or p.endswith('.log') or p.endswith('.txt')):continue
 if p.endswith(('.log','.txt')) and not any(x in p.lower() for x in ['kani','stdout','output','out.log','p6']):continue
 s=G.get(b).decode(errors='replace')
 if 'kani' not in s.lower() and 'CBMC' not in s and 'VERIFICATION' not in s:continue
 if p.endswith(('receipt.json','.json','.jsonl')):
  if 'kani' in s.lower():receipts.append(dict(path=p,blob=b,refs=refs,content=s))
 elif p.endswith('.md'):docs.append(dict(path=p,blob=b,refs=refs,content=s))
 elif 'Checking harness ' in s or 'VERIFICATION SUCCESSFUL' in s or 'CBMC version' in s:
  logs.append(dict(path=p,blob=b,refs=refs,harnesses=re.findall(r'Checking harness (.+)',s),success=s.count('VERIFICATION SUCCESSFUL'),failed=s.count('VERIFICATION FAILED'),copy_lines=[l[:500] for l in s.splitlines() if re.search(r'memcpy|memmove|copy_nonoverlapping|copy_from_slice|clone_from_slice|extend_from_slice|grow_amortized|realloc',l)],pins=[l[:500] for l in s.splitlines() if re.search(r'CBMC version|Kani Rust|cargo-kani 0|rustc 1\.',l)]))
(C/'receipt-census.json').write_text(json.dumps(receipts,indent=2)+'\n');(C/'log-census.json').write_text(json.dumps(logs,indent=2)+'\n');(C/'citation-census.json').write_text(json.dumps(docs,indent=2)+'\n')
print('receipts',len(receipts),'logs',len(logs),'docs',len(docs))
for x in logs:
 if x['success']:print(x['path'],x['success'],x['harnesses'][:3],len(x['copy_lines']))

# Select successful outputs with exact Kani success syntax, preserving source blobs.
passing=[]
for x in logs:
 if '/leaf-p6-' in x['path']:continue
 s=G.get(x['blob']).decode(errors='replace')
 if re.search(r'VERIFICATION(?::-|:)?.*SUCCESSFUL|Status: SUCCESS|0 failures',s):
  x['pass_harnesses']=re.findall(r'Checking harness (.+?)\.\.\.',s);passing.append(x)
(C/'passing-logs.json').write_text(json.dumps(passing,indent=2)+'\n')
