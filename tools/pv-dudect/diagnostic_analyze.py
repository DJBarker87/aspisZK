#!/usr/bin/env python3
"""diagnostic, not a V374 measurement; frozen crop formulas, histogram-weighted Welford."""
import csv,json,math,pathlib,sys,collections,hashlib
class Moments:
 def __init__(self):self.n=0;self.mean=0.;self.m2=0.
 def add(self,x,k):
  if not k:return
  n=self.n+k;d=x-self.mean;self.m2+=d*d*self.n*k/n;self.mean+=d*k/n;self.n=n
 def var(self):return self.m2/(self.n-1) if self.n>1 else 0.
def welch(a,b):
 v=a.var()/max(a.n,1)+b.var()/max(b.n,1)
 return dict(n=[a.n,b.n],means=[a.mean,b.mean],variances=[a.var(),b.var()],t=(a.mean-b.mean)/math.sqrt(v) if v else None)
report={}
for f in sorted(pathlib.Path(sys.argv[1]).glob('*.csv')):
 cal=[];hist=[collections.Counter(),collections.Counter()];bad=[0,0];accepted=[0,0];false=[0,0]
 with f.open() as stream:
  for row in csv.DictReader(stream):
   c=int(row['class']);x=int(row['cycles']);false[c]+=row['outcome']!='true'
   if row['valid']!='true':bad[c]+=1;continue
   accepted[c]+=1
   if len(cal)<20000:cal.append(x)
   else:hist[c][x]+=1
 center=sum(cal)/len(cal);cal.sort();cuts=[cal[min(len(cal)-1,int((1-0.5**(10*(i+1)/100))*len(cal)))] for i in range(100)]
 stats=[]
 for cut in [None]+cuts:
  a=[Moments(),Moments()];b=[Moments(),Moments()]
  for c in range(2):
   for x,k in sorted(hist[c].items()):
    if cut is None or x<cut:a[c].add(x,k);b[c].add((x-center)**2,k)
  stats.append(dict(cutoff=cut,**welch(*a),centered_square=welch(*b)))
 report[f.stem]=dict(label='diagnostic, not a V374 measurement',calibration_pooled=20000,valid=accepted,migrations=bad,false_outcomes=false,tests=stats,raw_sha256=hashlib.sha256(f.read_bytes()).hexdigest(),raw_bytes=f.stat().st_size,raw_path=str(f))
print(json.dumps(report,indent=2))
