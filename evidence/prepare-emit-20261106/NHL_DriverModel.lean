import NHL_DriverSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_DriverModel
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

def preparedOps (base expected : Ops) (reserved : Bool) : Ops :=
 NHL_PrepareModel.children (NHL_Packets.installed base reserved) expected

def txOps (base expected : Ops) (reserved : Bool) : Ops :=
 NHL_Tx1Model.children (preparedOps base expected reserved) expected

/-- The emitted tx1 actually calls the newly emitted prepare. CLOSED packet
slots stay fixed, and the four remaining child laws are only demanded at
reached cuts. No whole-function output or independent successful run is assumed. -/
theorem source (base expected : Ops) (reserved : Bool) {H : Type}
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H)
 (verify_observed : ∀ v, NHL_PrepareModel.Reaches base reserved D proof v →
   base.op9 D pub v.semantic hash none=expected.op9 D pub v.semantic hash none)
 (prepared_new : ∀ zero, aspis_core.field.wide_exact.WideExact.ZERO (NHL_Packets.installed base reserved)=ok zero →
   ∀ v sem, NHL_PrepareModel.Reaches base reserved D proof v →
   expected.op9 D pub v.semantic hash none=ok (.Ok sem) →
   base.op8 D sem v hash (Array.repeat 29#usize zero)=expected.op8 D sem v hash (Array.repeat 29#usize zero))
 (query_loop : ∀ c, NHL_Tx1Model.Reaches (preparedOps base expected reserved) expected
   D pub public_bytes proof k hash c →
   (preparedOps base expected reserved).op7 proof c.prepared c.accumulator c.scratch none c.geometry c.pending k=
   expected.op7 proof c.prepared c.accumulator c.scratch none c.geometry c.pending k)
 (checkpoint : ∀ c a pending, NHL_Tx1Model.Reaches (preparedOps base expected reserved) expected
   D pub public_bytes proof k hash c →
   expected.op7 proof c.prepared c.accumulator c.scratch none c.geometry c.pending k=ok (.Ok (a,pending)) →
   ∀ cells, (preparedOps base expected reserved).op17 pending (alloc.vec.Vec.deref_mut a.weights).1=ok cells →
   (preparedOps base expected reserved).op16 D c.prepared
     {a with weights:=(alloc.vec.Vec.deref_mut a.weights).2 cells} proof public_bytes hash=
   expected.op16 D c.prepared {a with weights:=(alloc.vec.Vec.deref_mut a.weights).2 cells} proof public_bytes hash) :
 NHL_EmittedTx1.tx1 (NHL_Packets.installed base reserved)
   (NHL_EmittedPrepare.prepare (NHL_Packets.installed base reserved)) D pub public_bytes proof k hash none=
 verifier.candidate.tx1 (txOps base expected reserved) D pub public_bytes proof k hash none := by
 rw [←NHL_DriverSlots.tx1 (NHL_Packets.installed base reserved) expected]
 apply NHL_Tx1Model.source (preparedOps base expected reserved) expected _ D pub public_bytes proof k hash
 · intro zero zeroCall
   rw [NHL_DriverSlots.prepare]
   have zeroOriginal : aspis_core.field.wide_exact.WideExact.ZERO (NHL_Packets.installed base reserved)=ok zero := by
     simpa only [preparedOps,NHL_PrepareModel.children,aspis_core.field.wide_exact.WideExact.ZERO] using zeroCall
   exact NHL_PrepareModel.source base expected reserved D pub proof hash (Array.repeat 29#usize zero)
     verify_observed (prepared_new zero zeroOriginal)
 · exact query_loop
 · exact checkpoint
#print axioms source
end AspisR1.NHL_DriverModel
