import re,sys
m,name=sys.argv[1:3]
s=open(f'../prov-p2g-20261109/PRVEq_{m}.lean').read()
for b in re.finditer(r'/- PRV-FRESH-DROPPED[^\n]*\n(.*?)\n-/\n',s,flags=re.S):
    t=b.group(1)
    if re.search(r'\ndef\s+'+re.escape(name)+r'\s*\n',t+'\n') or re.search(r'\ndef\s+'+re.escape(name)+r'\n',t) or ('\ndef '+name+'\n') in t: print('FRESH(dropped)\n'+t)
g=open(f'../prov-p2b-20261109/inputs/gate/{m}.lean').read()
for b in re.finditer(r'/-- \[.*?(?=\n/-- \[|\Z)',g,flags=re.S):
    if re.search(r'\ndef\s+'+re.escape(name)+r'\s*\n',b.group(0)): print('GATE\n'+b.group(0))
