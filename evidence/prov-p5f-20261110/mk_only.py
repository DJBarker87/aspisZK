import re,sys,json,os
M,out=sys.argv[1:3]
n=int(M.replace('RPu_FIq_Native',''))
names=[]
for i in range(1,n+1):
    f=f'inputs/RPu_FIq_Native{i:02d}.lean'
    if not os.path.exists(f): continue
    names+=re.findall(r'^def\s*\n?\s*(\S+)',open(f).read(),re.M)
names=[x for x in dict.fromkeys(names) if not x.endswith('.mutual') and not x.endswith('.body')]
json.dump(names,open(out,'w'))
loops=[x for x in names if re.search(r'_loop\d*(_loop\d*)*$',x)]
print(len(names),' '.join(loops))
