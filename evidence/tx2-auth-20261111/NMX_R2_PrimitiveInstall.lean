import NMX_R2_InverseBytes
import NMX_LeafInstall
set_option autoImplicit false
noncomputable section
namespace NMX_R2_PrimitiveInstall
open Aeneas Aeneas.Std Result AdapterRw NMX_R2_Carrier NMX_R2_InverseBytes
/-- Concrete std/key/PDA interpretation. The base slots for CLOSED decoders
and OPEN217/234 still need their typed installation; this is not a root. -/
def install (base : Ops) (env : RSL.Env) : Ops :=
 { NMX_LeafInstall.install base with
   op16 := ok 255#u8
   op37 := fun bytes => ok bytes
   op39 := fun key => ok key
   op40 := fun key => ok (Array.to_slice key)
   op38 := fun seeds program =>
     ok (match env.pda (seeds.val.map NMX_R2_Carrier.bytes) (NMX_R2_Carrier.key program) with
     | none => .Err .InvalidSeeds
     | some result => .Ok (fromKey result)) }

theorem fromBytes (base : Ops) (env : RSL.Env) (input : Array U8 32#usize) :
 (install base env).op37 input = ok input := rfl

theorem toBytes (base : Ops) (env : RSL.Env) (input : solana_pubkey.Pubkey) :
 (install base env).op39 input = ok input := rfl

theorem asRef (base : Ops) (env : RSL.Env) (input : solana_pubkey.Pubkey) :
 (install base env).op40 input = ok (Array.to_slice input) := rfl

/-- Exact ordered seed byte slices/program and quantified reply. No digest
value, chosen-success reply, address identity, or SHA/PDA evaluation is used. -/
theorem pda (base : Ops) (env : RSL.Env) (seeds : Slice (Slice U8))
 (program : solana_pubkey.Pubkey) :
 (install base env).op38 seeds program =
 ok (match env.pda (seeds.val.map NMX_R2_Carrier.bytes) (key program) with
 | none => .Err .InvalidSeeds
 | some output => .Ok (fromKey output)) := rfl
#print axioms fromBytes
#print axioms toBytes
#print axioms asRef
#print axioms pda
end NMX_R2_PrimitiveInstall
end
