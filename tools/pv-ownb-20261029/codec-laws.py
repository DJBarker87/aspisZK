from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-ownb-20261029'
names=['spongeCarry','ownerOutput','nullifierKey','inputSaltHead','inputSaltTail','privatePathCurrent','privatePathLeft','privatePathRight','valueSource','conservationInput','conservationRecipient','conservationChange','conservationPartial','inputSecondCommitment','inputSelectedSide','outputSecondCommitment','outputPairFirst','outputPairFirstWithdrawal','outputPairSecond','appendCurrentLeft','appendCurrentRight']
q=[]
for t,k in enumerate(names):
 arity=2 if t==0 else 1 if t in [5,6,7,8,19,20] else 0
 m='PV_OWNB_Kind'+str(t).zfill(2);args=' '.join(['a','b'][:arity]);vs=(' ('+args+' : UInt8)') if arity else ''
 hs='\n'.join(f' (h{i+1}:raw {i+1}=some {a})'for i,a in enumerate(['a','b'][:arity]))
 s=f'''import R1Z.PV_OWNB_KindCodec
set_option autoImplicit false
namespace R1Z.{m}
open PV_OWN_Link PV_OWNB_KindCodec
/-- Active-field read for variant {t}; no constraint on padding bytes. -/
theorem read (raw : Nat → Option UInt8){vs}
 (h0:raw 0=some ({t}:UInt8)){hs} :
 decode raw=some (Kind.{k}{(' '+args) if args else ''}) := by
 simp [decode,h0{''.join(',h'+str(i+1)for i in range(arity))}]
#print axioms read
end R1Z.{m}
'''
 (L/(m+'.lean')).write_text(s);q.append(f'{62510+t} R1Z/{m}')
(E/'kind-targets.txt').write_text('\n'.join(q)+'\n')
