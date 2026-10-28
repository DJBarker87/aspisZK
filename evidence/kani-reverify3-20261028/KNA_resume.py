"""Continue retired timeout shapes only via narrower observation windows."""
from KNA_runtime import *

def query_window(cap,ilo,ihi,lo,hi,tail=False):
 obs=(f'let b:usize=kani::any();kani::assume(b<4);let j=len+b;' if tail else f'let j:usize=kani::any();kani::assume({lo}<=j && j<{hi} && j<len);assert_eq!(out[j],initial[j]);')
 return f'''let initial:[u8;{cap}]=kani::any();let source:[u8;4]=kani::any();
let i:usize=kani::any();kani::assume({ilo}<=i && i<{ihi});let len=64+4*i;
let mut out=alloc::vec::Vec::from(initial);out.truncate(len);
assert_eq!(out.len(),len);assert_eq!(out.capacity(),{cap});
{obs}
KMX_stubs::KMX_extend_from_slice(&mut out,&source);
assert_eq!(out.len(),len+4);assert_eq!(out.capacity(),{cap});
assert_eq!(out[j],(if j<len{{initial[j]}}else{{source[j-len]}})^NEG);
'''

def main():
 # First attempt every previously unrun arbitrary-length frame draft.
 for name in ['selected','append32','append4','append16']:pair(name,draft(name))
 # Finish all previously unrun prescribed body windows, including appended32.
 for w in range(5,12):
  lo=160*w if w<11 else 1736;hi=min(1736,lo+160) if w<11 else 1768
  pair(f'body_{lo}_{hi}',BASE+ATTR+f'fn KNA_body_{lo}_{hi}(){{'+bodywindow(lo,hi)+'}\n')
 # Retired first five parents: halve each observation interval.
 for w in range(5):
  lo=160*w;mid=lo+80;hi=lo+160
  for a,b in [(lo,mid),(mid,hi)]:pair(f'body_{a}_{b}',BASE+ATTR+f'fn KNA_body_{a}_{b}(){{'+bodywindow(a,b)+'}\n')
 # Direct constructors retained; split both association observations and appended bytes.
 for cap,ilo,ihi,windows in [(128,1,16,[(0,64),(64,124)]),(256,17,22,[(0,64),(64,128),(128,148)])]:
  for lo,hi in windows+[(0,0)]:
   tail=hi==0;name=f'query_{cap}_'+('tail' if tail else f'{lo}_{hi}')
   pair(name,BASE+ATTR.replace('1769','258')+f'fn KNA_{name}(){{'+query_window(cap,ilo,ihi,lo,hi,tail)+'}\n')
 # Byte observation splits on one actual append and one arbitrary symbolic length.
 for name in ['selected','append32','append4','append16']:
  p=next(x for x in json.loads((E/'KNA_PAIRS.json').read_text()) if x['name']==name)
  if not p['credit']:
   for lo,hi in [(0,884),(884,1768)]:pair(f'{name}_byte_{lo}_{hi}',draft(name,lo,hi))
 # Remaining budget follows first uncredited body child, strictly halving its parent.
 while len(list(E.glob('KNA_K[0-9][0-9][0-9].json')))<90:
  records=json.loads((E/'KNA_PAIRS.json').read_text());by={x['name']:x for x in records}
  candidates=[]
  for p in records:
   if p['credit'] or not p['name'].startswith('body_'):continue
   _,a,b=p['name'].split('_');a=int(a);b=int(b);m=(a+b)//2
   if b-a<=1:continue
   for lo,hi in [(a,m),(m,b)]:
    if f'body_{lo}_{hi}' not in by:candidates.append((b-a,lo,hi))
  if not candidates:break
  _,lo,hi=sorted(candidates,reverse=True)[0]
  pair(f'body_{lo}_{hi}',BASE+ATTR+f'fn KNA_body_{lo}_{hi}(){{'+bodywindow(lo,hi)+'}\n')
if __name__=='__main__':main()
