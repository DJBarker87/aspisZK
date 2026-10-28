from pathlib import Path
P=Path('lean')
source=Path('docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean').read_text()
body=source.split('def pool_v1.payment_relation.encode_common ',1)[1].split(' := do\n',1)[1].split('\n\n/--',1)[0]
markers=['  let (s3,','  let (s6,','  let (s9,','  let (s12,','  let (s15,','  let (s18,']
positions=[0]+[body.index(m) for m in markers]+[len(body)]
rows={1:(8,40,'common.pool'),2:(40,72,'common.deployment_domain'),3:(72,80,'(core.num.U64.to_le_bytes common.anchor_sequence)'),4:(80,112,'(AspisR1.S2K.DigestBytes.bytes common.anchor_root)'),5:(112,144,'(AspisR1.S2K.DigestBytes.bytes common.nullifier)'),6:(144,148,'(core.num.U32.to_le_bytes common.asset_id)')}
inputs=['output','output4','output5','output6','output7','output8','output9']
for i in reversed(range(7)):
 name=f'NBP_CommonTail{i}';dep=f'NBP_CommonTail{i+1}' if i<6 else 'NBP_DigestEncode'
 s=f'''import {dep}
import NBP_ArrayIndex
import NBP_Store
import NBG_Header
set_option autoImplicit false
noncomputable section
namespace {name}
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind
'''
 args='(output : Array U8 216#usize) '+('(magic : Array U8 4#usize) (kind : K) ' if i==0 else '')+'(common : C)'
 b=body[positions[i]:positions[i+1]].replace(inputs[i],'output')
 if i<6:b+=f'  NBP_CommonTail{i+1}.run {inputs[i+1]} common\n'
 s+=f'\ndef run {args} : Result (Array U8 216#usize) := do\n'+b+'\n'
 if i:
  start,stop,expr=rows[i]
  ret=f'output.setSlice! {start} {expr}.val'
  end=ret if i==6 else f'NBP_CommonTail{i+1}.expected ({ret}) common'
  s+=f'def expected {args} : Array U8 216#usize :=\n  {end}\n'
 else:
  s+='''def expected (output : Array U8 216#usize) (magic : Array U8 4#usize) (kind : K) (common : C) : Array U8 216#usize :=
  let output := output.setSlice! 0 magic.val
  let output := output.set 4#usize 1#u8
  let output := output.set 5#usize (NBG_Header.tag kind)
  let output := output.set 6#usize 1#u8
  NBP_CommonTail1.expected output common
'''
 actual='run output '+('magic kind ' if i==0 else '')+'common';ex='expected output '+('magic kind ' if i==0 else '')+'common'
 s+=f'\ntheorem result {args} : {actual} = ok ({ex}) := by\n  unfold run\n'
 s+='''  simp only [pool_v1.payment_relation.POOL_OFFSET,pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,NBP_DigestEncode.result,NBG_Header.tag_result,
    aspis_core.field.M31.to_le_bytes,lift,bind_tc_ok]
'''
 if i==0:
  start,stop,expr=0,4,'magic'
  s+='  rw [NBP_ArrayIndex.prefix_index output 4#usize (by decide)]\n'
 else:s+=f'  rw [NBP_ArrayIndex.index_mut output {start}#usize {stop}#usize (by decide) (by decide)]\n'
 s+=f'''  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8
      (NBP_ArrayIndex.slice output {start}#usize {stop}#usize) {expr}.to_slice
    _) = _
  rw [NBP_ArrayIndex.copy_range output {start}#usize {stop}#usize {expr} (by decide) (by decide) (by decide)]
  simp only [bind_tc_ok]
'''
 if i==0:
  for k,v in [(4,'1#u8'),(5,'(NBG_Header.tag kind)'),(6,'1#u8')]:s+=f'  rw [NBP_Store.update _ {k}#usize {v} (by decide),bind_tc_ok]\n'
 if i<6:s+=f'  rw [NBP_CommonTail{i+1}.result]\n'
 s+='  rfl\n#print axioms result\nend '+name+'\n'
 (P/(name+'.lean')).write_text(s)
# Source assembly uses actual frozen operation bodies, not an independently
# selected successful execution or invented operation dictionary.
s='''import NBP_CommonTail0
set_option autoImplicit false
noncomputable section
namespace NBP_CommonBytes
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev C := pool_v1.payment_relation.CommonPublicV1
abbrev K := pool_v1.historical_anchor.PoolV1TransitionKind
abbrev encoded := NBP_CommonTail0.expected

theorem association (output : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) (c : C) :
    pool_v1.payment_relation.encode_common output magic kind c =
      NBP_CommonTail0.run output magic kind c := by
  unfold pool_v1.payment_relation.encode_common
'''
s+='  unfold '+' '.join(f'NBP_CommonTail{i}.run' for i in range(7))+'\n  rfl\n'
s+='''theorem result (output : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : K) (c : C) :
    pool_v1.payment_relation.encode_common output magic kind c = ok (encoded output magic kind c) := by
  rw [association]
  exact NBP_CommonTail0.result output magic kind c
#print axioms association
#print axioms result
end NBP_CommonBytes
'''
(P/'NBP_CommonBytes.lean').write_text(s)
