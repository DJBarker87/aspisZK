from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=''.join(f'import R1Z.PV_OWNB_Kind{i:02}\n' for i in range(21))+'import R1Z.PV_OWNB_Padding\n'
s+='''set_option autoImplicit false
namespace R1Z.PV_OWNB_KindAgreement
open PV_OWN_Link PV_OWNB_KindCodec PV_OWNB_Padding
/-- Active-byte agreement suffices; inactive bytes may contain arbitrary data. -/
theorem read (k : Kind) (raw : PV_OWN_Bytes.Bytes) (h:Agrees (encode k) raw) :
 decode raw=some k := by
 cases k with
'''
names=['spongeCarry','ownerOutput','nullifierKey','inputSaltHead','inputSaltTail','privatePathCurrent','privatePathLeft','privatePathRight','valueSource','conservationInput','conservationRecipient','conservationChange','conservationPartial','inputSecondCommitment','inputSelectedSide','outputSecondCommitment','outputPairFirst','outputPairFirstWithdrawal','outputPairSecond','appendCurrentLeft','appendCurrentRight']
for t,k in enumerate(names):
 arity=2 if t==0 else 1 if t in [5,6,7,8,19,20] else 0
 vs=' '.join(['a','b'][:arity]);s+=f' | {k}{(" "+vs)if vs else ""} =>\n  apply PV_OWNB_Kind{t:02}.read\n'
 for i in range(arity+1):
  b=f'({t}:UInt8)' if i==0 else ['a','b'][i-1]
  s+=f'  exact h {i} {b} (by simp [encode,tag,first,second])\n'
s+='''
theorem unique (a b : Kind) (raw : PV_OWN_Bytes.Bytes)
 (ha:Agrees (encode a) raw) (hb:Agrees (encode b) raw) : a=b := by
 exact Option.some.inj ((read a raw ha).symm.trans (read b raw hb))
#print axioms read
#print axioms unique
end R1Z.PV_OWNB_KindAgreement
'''
(L/'PV_OWNB_KindAgreement.lean').write_text(s)
