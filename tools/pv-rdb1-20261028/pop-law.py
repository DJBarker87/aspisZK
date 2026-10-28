"""Freeze the unchanged complete value/world proof under private names.
Only namespace/import changes: a checked embedding, not an edited extraction.
"""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2]; L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'; E=R/'evidence/pv-rdb1-20261028'
names=['PV_CBL_VectorPopSpec','PV_AL_PopLast','PV_AL_RemoveModel','PV_AL_PopWorld','PV_AL_MoveFacts','PV_AL_MoveLast','PV_AL_MoveMemory','PV_AL_MoveNativeValue','PV_AL_MoveWorld']
mapping={n:'PV_RDB1_V184_'+n.split('_',2)[2] for n in names}
parts=['import R1Z.PV_RDB1_Pointer\n'];pins=[]
for n in names:
 p=L/(n+'.lean');s=p.read_text(); t='\n'.join(l for l in s.splitlines() if not l.startswith('import '))+'\n'
 for a,b in mapping.items(): t=t.replace(a,b)
 parts.append(t)
 pins.append(dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(s.encode()).hexdigest(),private_namespace=mapping[n],change='imports removed and namespace identifiers renamed only'))
parts.append('''
namespace R1Z.PV_RDB1_V184
open Aeneas Aeneas.Std Result
open PV_RDB1_Pointer

/-- Complete Result and world observation at the original structural library
boundary. Pointer representation has been resolved by cast_complete; the
carrier, read/header/copy and intrinsic semantics retain their original scope. -/
theorem complete {T F : Type} (b : PV_RDB1_V184_PopWorld.Buffer T)
    (w : PV_RDB1_V184_PopWorld.World) (memory : PV_RDB1_V184_MoveMemory.Memory)
    (frame : F) (width : Nat) :
    ∃ o : PV_RDB1_V184_MoveMemory.Observation T F,
      PV_RDB1_V184_MoveWorld.nativeWorld b w memory frame = ok o ∧
      PV_RDB1_V184_MoveWorld.referenceWorld b w memory frame width = ok o ∧
      o.returned = b.value.val.getLast? ∧ o.remaining.val = b.value.val.dropLast ∧
      o.buffer = b.address ∧ o.capacity = b.capacity ∧ o.world = w ∧
      o.memory = memory ∧ o.frame = frame := by
  refine ⟨PV_RDB1_V184_MoveWorld.expected b w memory frame,
    PV_RDB1_V184_MoveWorld.native_complete b w memory frame,
    PV_RDB1_V184_MoveWorld.reference_complete b w memory frame width,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Deployed casting followed by add reaches exactly the initialized slot the
retained read semantics consume, including provenance and width zero. -/
theorem read_address {T P : Type} (p : NonNull T P) (n width : Nat) :
    (offset (asPtr (deployedCast (U := T) p)) (n-1) width).address =
      p.pointer.address + (n-1)*width ∧
    (offset (asPtr (deployedCast (U := T) p)) (n-1) width).provenance =
      p.pointer.provenance := ⟨rfl,rfl⟩

#print axioms complete
#print axioms read_address
end R1Z.PV_RDB1_V184
''')
(L/'PV_RDB1_V184.lean').write_text('\n'.join(parts))
(E/'v184-model-embedding.json').write_text(json.dumps(dict(mapping=mapping,source_pins=pins,interpretation='Unchanged model laws; source association is separately checked by deployed-pop-gate.py. Original dictionary selected/consumed proof unchanged, not substituted by this embedding.'),indent=2)+'\n')
