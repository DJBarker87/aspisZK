"""Specialize the installed source entry to actual opsNative and its guard."""
from pathlib import Path
import hashlib,json,re,sys
E=Path('evidence/pv-evh8-20261101');p=Path('lean/PV_EVH_OperatorProver.lean');s=p.read_text()
s=s.replace('namespace PV_EVH_OperatorProver','namespace PV_EVH_NativeOperatorProver').replace('end PV_EVH_OperatorProver','end PV_EVH_NativeOperatorProver')
s='import PV_EVH_NativeOperatorGuard\n'+s
s=s.replace('variable [ExternalTypes] [ExternalFuns]', '''open R1Z.PV_RunJoin_NativeResidual62
variable (base : ExternalTypes) (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
  (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
local instance : ExternalTypes := types base
variable (ops : @ExternalFuns (types base))
local instance : ExternalFuns := opsNative base heap box ops''')
s=s.replace('    (guard_OPEN : transport.Variant → P Bool)\n','')
guard='''    (guard_fixed : ∀ v, FinishedView (guard_OPEN v)
      (core.cmp.PartialEq.ne.trait_default transport.Variant.Insts.CoreCmpPartialEqVariant v transport.Variant.S2))
'''
assert s.count(guard)==1;s=s.replace(guard,'')
s=s.replace('    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :', '    :')
s=s.replace('FinishedView (entry_OPEN inst','FinishedView (entry_OPEN base heap box ops inst')
# The new wrapper removes its guard argument; the delegated source entry keeps it.
start=s.index('FinishedView (entry_OPEN base');end=s.index(')\n      (RealR1_client',start)
s=s[:start]+s[start:end].replace('nonceCallees guard_OPEN','nonceCallees')+s[end:]
s=re.sub(r'\bguard_OPEN\b','PV_EVH_VariantGuard.guard',s)
s=re.sub(r'\bguard_fixed\b','(PV_EVH_NativeOperatorGuard.guard_view base heap box ops)',s)
s=re.sub(r'\bselected\b','(PV_EVH_NativeOperators.selection base heap box ops)',s)
q=Path('lean/PV_EVH_NativeOperatorProver.lean');r=E/'native-operator-prover-generation.json';out=json.dumps(dict(source=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(s.encode()).hexdigest(),status='actual dictionary selection installed; native leaf/frame/runtime adequacy OPEN',rows_removed=[]),indent=2)+'\n'
if '--check' in sys.argv:assert q.read_text()==s and r.read_text()==out
else:q.write_text(s);r.write_text(out)
print('Actual dictionary/variant selection installed into source entry')
