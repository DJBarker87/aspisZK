from NEK_box_context import *
for num,idx in [(76,311),(77,312)]:
 a=f'NEK_K{idx:03}'
 if (E/a/'receipt.json').exists():continue
 rp=f'evidence/slice-s-leaves-20261029/NEC_K{num:03}/receipt.json';o,method=make(rp)
 v=publish(a,rp,o,num==77,method)
 if v=='OPEN':break
