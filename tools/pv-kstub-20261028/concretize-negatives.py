"""Wrong-property controls on concrete, nonempty, nonzero admitted fixtures.
Positive proof bodies, assumptions, and KMX source are unchanged.
"""
from pathlib import Path
import re,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-kstub-20261028');changes=[]
fixtures={
'cb':{'string_ascii8':{'bytes':'[65;8]','len':'8'},'string_scalar':{'scalar':'65'},'push_ascii1':{'a':'65','b':'66'}},
'cblib':{'join_one_byte':{'a':'[65;1]','b':'[66;1]','n':'1','m':'1','i':'0'},'string_path':{'raw':'[65;2]','i':'0'},'string_push':{'raw':'[65;2]','tail':'[66;1]','i':'0'},'join_two':{'a':'[65;2]','b':'[66;2]','n':'2','m':'2','i':'0'},'push_bytes':{'raw':'[65;2]','tail':'[66;1]'},'join_slices_two':{'a':'[65;2]','b':'[66;2]','n':'2','m':'2','i':'0'}},
'wide':{'wide_flat':{'raw':'[0x01020304;8]'}},
'native/core':{'all_carriers':{'w':'[0x01020304;8]'}},
'split':{'split64_coordinate_lo':{'data':'[65;129]','n':'63','b':'0','j':'0','k':'0'},'split64_coordinate_hi':{'data':'[65;129]','n':'65','b':'0','j':'0','k':'0'}}}
def function(s,name):
 a=s.index('fn '+name+'(');b=s.index('{',a);i=b+1;d=1
 while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
for pkg,fs in fixtures.items():
 p=D/pkg/('src/field/wide_exact.rs' if pkg=='native/core' else 'src/sealed.rs' if pkg=='split' else 'lib.rs');s=p.read_text()
 for h,vals in fs.items():
  name=h+'_negative';old=function(s,name);new=old
  for var,value in vals.items():
   pattern=r'(let\s+'+var+r'\s*:[^;=]+?=\s*)kani::any\(\)'
   # Array type includes its size semicolon; permit that in the declaration.
   pattern=r'(let\s+'+var+r'\s*:\s*(?:\[[^\]]+\]|\w+)\s*=\s*)kani::any\(\)'
   new,n=re.subn(pattern,lambda m:m[1]+value,new)
   if n==0:assert re.search(pattern.replace(r'kani::any\(\)',re.escape(value)),new),(pkg,name,var,n)
  s=s.replace(old,new);changes.append(dict(package=pkg,harness=name,fixture=vals,before_sha256=hashlib.sha256(old.encode()).hexdigest(),after_sha256=hashlib.sha256(new.encode()).hexdigest()))
 p.write_text(s)
(D/'negative-fixtures.json').write_text(json.dumps(changes,indent=2));print(len(changes),'negative controls concretized; running K03 untouched')
