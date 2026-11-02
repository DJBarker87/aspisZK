"""Exact NDN inherited matrix instrument, including its additional reply assignment."""
from NEK_priority import *
def run(start=303):
 rp='evidence/native-front2b-20261028/NDN_K001/receipt.json'
 o=read_json(E/'NEK_K001_overlay.json');p='crates/aspis-statement/src/state_only_poseidon.rs'
 old='#[cfg(all(kani,NDE_matrix_step))]\n    return [0;4];'
 new='#[cfg(all(kani,NDE_matrix_step))]\n    {ctx.NDE_MATRIX_REPLY=local[ctx.NDE_PACKED_ROW][ctx.NDE_PACKED_LIMB];return [0;4];}'
 assert old in o[p];o[p]=o[p].replace(old,new)
 # The receipt uses NDE_window_invert, in distinction to NDE_K050.
 m='crates/aspis-statement/src/NDE_poseidon.rs';o[m]=o[m].replace('cfg!(NDE_invert)','cfg!(NDE_window_invert)')
 for neg in [False,True]:
  a=f'NEK_K{start+int(neg):03}'
  if (E/a/'receipt.json').exists():continue
  oo=dict(o)
  if neg:oo[m]=oo[m].replace('!= cfg!(NDE_window_invert)','== cfg!(NDE_window_invert)')
  v=publish(a,rp,oo,neg,'NDN exact inherited matrix property/name, extra local reply assignment retained; explicit native-step context')
  if v=='OPEN':break
if __name__=='__main__':run()
