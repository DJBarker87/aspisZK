from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rdb1-20261028'
names=['PV_FXM_ReserveWorld','PV_FXM_ReserveLayout','PV_FXM_ReserveFacts','PV_FXM_ReservePrimitive'];mapping={n:n.replace('PV_FXM_','PV_RDB1_V183_') for n in names}
parts=['import R1Z.PV_RDB1_Layout\nimport R1Z.PV_RDB1_PointerConstruct\n'];pins=[]
for n in names:
 p=L/(n+'.lean');s=p.read_text();t='\n'.join(x for x in s.splitlines() if not x.startswith('import '))+'\n'
 for a,b in mapping.items():t=t.replace(a,b)
 parts.append(t);pins.append(dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(s.encode()).hexdigest(),private_namespace=mapping[n],change='imports and namespaces only'))
parts.append('''
namespace R1Z.PV_RDB1_V183
open Aeneas Aeneas.Std Result PV_RDB1_V183_ReserveWorld

/-- Deployed repeat maps away the returned stride. Actual Rust element
layouts have power-of-two alignment and size a multiple of it; pad_element
proves the exact machine mask leaves such a layout unchanged. -/
theorem element_repeat_complete (wordBits alignBits k wordMax byteMax n : Nat)
    (representable : 2^alignBits*k < 2^wordBits) :
    (match PV_RDB1_Layout.packed wordMax byteMax
        (PV_RDB1_Layout.pad wordBits ⟨2^alignBits*k,2^alignBits⟩) n with
     | .error e => Except.error e
     | .ok repeated => Except.ok (repeated,
         (PV_RDB1_Layout.pad wordBits ⟨2^alignBits*k,2^alignBits⟩).size)).map Prod.fst =
      PV_RDB1_Layout.packed wordMax byteMax ⟨2^alignBits*k,2^alignBits⟩ n :=
  PV_RDB1_Layout.repeat_complete wordMax byteMax n _ _
    (PV_RDB1_Layout.pad_element wordBits alignBits k representable)

/-- Same full Result/effect carrier as the consumed reserve law, including
capacityOverflow, allocation error payload and allocator private state. -/
theorem complete {T S F : Type} (step : Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Shape) (b : Buffer T)
    (additional : Nat) (w : World S F) :
    native step wordMax byteMax shape b additional w =
      reference step wordMax byteMax shape b additional w :=
  source_reference step wordMax byteMax shape b additional w

structure Runtime (S F : Type) where
  allocator : S
  bytes : Nat → Option Nat
  external : F

/-- Allocator-accessible bytes and external observations are retained inside
its arbitrary private state, on success AND null return. Logical allocation
snapshots do not assert preservation of freed physical memory. -/
theorem physical_effect {T S F D : Type}
    (step : Request → Runtime S F → Option Nat × Runtime S F)
    (shape : Shape) (b : Buffer T) (additional : Nat) (w : World (Runtime S F) D) :
    let req : Request := ⟨b.address,b.capacity,b.values.length+additional,shape⟩
    (finish step shape b additional w).world.allocator.bytes = (step req w.allocator).2.bytes ∧
    (finish step shape b additional w).world.allocator.external = (step req w.allocator).2.external := by
  have h := PV_RDB1_V183_ReserveFacts.finish_effects step shape b additional w
  exact ⟨congrArg Runtime.bytes h.1,congrArg Runtime.external h.1⟩

#print axioms element_repeat_complete
#print axioms complete
#print axioms physical_effect
end R1Z.PV_RDB1_V183
''')
(L/'PV_RDB1_V183.lean').write_text('\n'.join(parts));(E/'v183-model-embedding.json').write_text(json.dumps(dict(mapping=mapping,source_pins=pins),indent=2)+'\n')
