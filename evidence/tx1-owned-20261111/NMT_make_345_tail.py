from pathlib import Path
import re,textwrap,json
E=Path(__file__).resolve().parent
s=(E/'NMT_345Raw_11.lean').read_text();body=s[s.index(' let i1 :='):s.index('\nend NMT_345')]
frames='''import NMT_345Raw_11
import NMT_345Raw_12
import NMT_345Semantic
set_option autoImplicit false
namespace NMT_345
open Aeneas Aeneas.Std
structure HasPrefix (W : Type) extends Bounds W where
 proofPrefix : Slice U8
structure PrefixReply (W : Type) extends HasPrefix W where
 prefixMismatch : Bool
structure TagOffset (W : Type) extends PrefixReply W where
 tagOffset : Usize
structure TagByte (W : Type) extends TagOffset W where
 tagByte : U8
structure TagExpected (W : Type) extends TagByte W where
 expectedTag : U8
structure HasPublic (W : Type) extends TagExpected W where
 semanticPublic : Public
structure HasProofSlice (W : Type) extends HasPublic W where
 proofSlice : Slice U8
structure HasSplitByte (W : Type) extends HasProofSlice W where
 splitByte : U8
structure HasSplit (W : Type) extends HasSplitByte W where
 split : Usize
end NMT_345
'''
(E/'NMT_345TailFrames.lean').write_text(frames)
plans=[
 ('PrefixRead','let s ←','Bounds',{}),
 ('PrefixCompare','let b1 ←','HasPrefix',{'s':'proofPrefix'}),
 ('PrefixReply','if b1','PrefixReply',{'b1':'prefixMismatch'}),
 ('TagOffset','let i2 ←','PrefixReply',{}),
 ('TagRead','let i3 ←','TagOffset',{'i2':'tagOffset'}),
 ('TagExpected','let i4 ←','TagByte',{'i3':'tagByte'}),
 ('TagReply','if i3 != i4','TagExpected',{'i3':'tagByte','i4':'expectedTag'}),
 ('SemanticRead','let p ←','TagExpected',{}),
 ('ProofRange','let s1 ←','HasPublic',{'p':'semanticPublic'}),
 ('SplitByte','let i5 ←','HasProofSlice',{'p':'semanticPublic','s1':'proofSlice'}),
 ('SplitCast','let i6 ←','HasSplitByte',{'p':'semanticPublic','s1':'proofSlice','i5':'splitByte'}),
 ('Child','let r14 ←','HasSplit',{'p':'semanticPublic','s1':'proofSlice','i6':'split'})]
for label,start,phase,mapping in plans:
 at=body.index(start);at=body.rfind('\n',0,at)+1;b=textwrap.dedent(body[at:])
 if mapping:b=re.sub(r'(?<![.\w])('+ '|'.join(mapping)+r')\b',lambda m:'parent.'+mapping[m[1]],b)
 t='''import NMT_345TailFrames
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
'''+f'def tail{label} {{W : Type}} (c : Calls) (parent : {phase} W) : Result Ret := do\n'+textwrap.indent(b,' ')+'\nend NMT_345\n'
 (E/('NMT_345Tail'+label+'.lean')).write_text(t)
(E/'NMT_345_TAIL_PLAN.json').write_text(json.dumps([dict(label=l,phase=p,module='NMT_345Tail'+l,cut=start)for l,start,p,m in plans],indent=1)+'\n')
