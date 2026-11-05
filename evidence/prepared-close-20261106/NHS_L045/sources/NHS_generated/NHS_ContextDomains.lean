import NHS_Tx1Context
import NHS_PrepareFields
import NHS_PrepareScratch
import NGK_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_ContextDomains
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- The actual reached Context supplies NFS's two domains and NGC's immutable
fields. Initializers are taken from that SAME prefix, never selected separately.
This is a model-domain consumer, not closure of the native TX1 driver. -/
theorem source {F C H : Type} (configuration : DrvC_Installation.Configuration F C)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (publicBytes proof : Slice U8) (k : Usize) (hash : H) (ctx : NHL_Tx1Stages.Context)
 (run : NHL_Tx1Stages.beforeQuery
   (DrvC_Installation.currentInstalled (F3V_Install.configuration configuration))
   (verifier.candidate.prepare (DrvC_Installation.currentInstalled (F3V_Install.configuration configuration)))
   D pub publicBytes proof k hash none=ok (.Ok ctx)) :
 NGC_PreparationBoundary.Fields (Tx1Q_Carriers.prepared ctx.prepared) ∧
 NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray (Tx1Q_Carriers.arr Tx1Q_Carriers.e ctx.scratch)) ∧
 NFS_QueryInvariant.Domain (Tx1Q_Carriers.prepared ctx.prepared) 0 10
   (Tx1Q_Carriers.accumulator ctx.accumulator) (Tx1Q_Carriers.pending ctx.pending) ∧
 ctx.accumulator.next.val=0 := by
 let installed := DrvC_Installation.currentInstalled (F3V_Install.configuration configuration)
 obtain ⟨zero,p,g,a,geometry,b,zeroCall,prepared,initial,geo,pending,same⟩ :=
   NHS_Tx1Context.source installed (verifier.candidate.prepare installed)
     D pub publicBytes proof k hash ctx run
 subst ctx
 have fields := NHS_PrepareFields.installed
   (DrvC_Installation.current (F3V_Install.configuration configuration)) configuration.boundaries configuration.std
   D hash pub proof _ g p prepared
 have canonical := NHS_PrepareScratch.source
   (DrvC_Installation.current (F3V_Install.configuration configuration))
   (F3M_CircleSource.install configuration.boundaries) configuration.std D hash pub proof p _ g prepared
 change Tx1Q_PrefixInstall.initial configuration.reserved .S2=ok (.Ok a) at initial
 change Tx1Q_PrefixInstall.newPending configuration.reserved a.weights.deref=ok (.Ok b) at pending
 have newA := Tx1Q_PrefixInstall.initial_success configuration.reserved a initial
 have newB := Tx1Q_PrefixInstall.pending_success configuration.reserved a.weights.deref b pending
 have initialCall : (Port3_Constructor.installed configuration.stageBase configuration.reserved).op12 .S2=
   ok (.Ok (Tx1Q_Carriers.accumulator a)) :=
   (NGC_Initialization.constructor configuration.stageBase configuration.reserved .S2).trans newA
 have both := NGC_InitialInvariant.initial configuration.stageBase configuration.reserved configuration.reserved
   (Tx1Q_Carriers.prepared p) (Tx1Q_Carriers.accumulator a) (Tx1Q_Carriers.pending b) fields initialCall newB
 exact ⟨fields,canonical,both.1,both.2⟩
#print axioms source
end AspisR1.NHS_ContextDomains
