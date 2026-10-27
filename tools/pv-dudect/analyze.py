#!/usr/bin/env python3
"""Offline preregistered Welch analysis; never runs a kernel or starts a window.

Dudect percentile cropping: 100 cutoffs 1 - 0.5**(10*(i+1)/100).
Cutoffs are frozen from the first 20,000 pooled, valid observations per family.
These calibration observations are excluded from all tests. Both classes use
identical strict cycle cutoffs. Keep the uncropped test and every cropped test;
no 'best crop', early stopping, or deletion of outliers from retained raw CSV.
"""
import csv,json,math,pathlib,sys,bisect
class Moments:
 def __init__(self):self.n=0;self.mean=0.;self.m2=0.
 def add(self,x):
  self.n+=1;d=x-self.mean;self.mean+=d/self.n;self.m2+=d*(x-self.mean)
 def var(self):return self.m2/(self.n-1) if self.n>1 else 0.
def welch(a,b):
 v=a.var()/max(a.n,1)+b.var()/max(b.n,1)
 return dict(n=[a.n,b.n],means=[a.mean,b.mean],variances=[a.var(),b.var()],t=(a.mean-b.mean)/math.sqrt(v) if v else None)
root=pathlib.Path(sys.argv[1]);report={}
for f in sorted(root.glob('*.csv')):
 cal=[];cuts=None;tests=None;second=None;center=None;bad=[0,0];accepted=[0,0]
 for row in csv.DictReader(f.open()):
  c=int(row['class']);x=int(row['cycles'])
  if row['valid']!='true':bad[c]+=1;continue
  accepted[c]+=1
  if len(cal)<20000:
   cal.append(x)
   if len(cal)==20000:
    center=sum(cal)/len(cal);cal.sort();cuts=[cal[min(len(cal)-1,int((1-0.5**(10*(i+1)/100))*len(cal)))] for i in range(100)]
    tests=[[Moments(),Moments()] for _ in range(101)];second=[[Moments(),Moments()] for _ in range(101)]
   continue
  for j,cut in enumerate([None]+cuts):
   if cut is None or x<cut:tests[j][c].add(x);second[j][c].add((x-center)**2)
 assert tests is not None, f'{f}: insufficient calibration'
 stats=[dict(cutoff=cut,**welch(*pair),centered_square=welch(*sq)) for cut,pair,sq in zip([None]+cuts,tests,second)]
 report[f.stem]=dict(calibration_pooled=20000,cutoff_probabilities=[1-0.5**(10*(i+1)/100) for i in range(100)],valid=accepted,migrations=bad,tests=stats,threshold=4.5,diagnostic_trigger=any(s['t'] is not None and abs(s['t'])>4.5 or s['centered_square']['t'] is not None and abs(s['centered_square']['t'])>4.5 for s in stats),interpretation='multiple correlated diagnostic tests; no detection is not a proof of constant time')
print(json.dumps(report,indent=2,allow_nan=False))
