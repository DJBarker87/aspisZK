import NHL_Tx1Frame
import NFW_PrepareQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_Tx1Model
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NHL_Tx1Stages

/-- The same prefix constructs the entire context entering the query loop. -/
def Reaches (base expected : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H) (c : Context) : Prop :=
 beforeQuery base (verifier.candidate.prepare (children base expected))
   D pub public_bytes proof k hash none=ok (.Ok c)

/-- Conditional full tx1, including every rejection and the SAME final writer
input. NFS supplies the query packet once its derived producer domain is
installed; checkpoint remains OPEN on that preparation predicate. -/
theorem source (base expected : Ops) {H : Type} (first : NHL_EmittedTx1.Prepare H)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H)
 (prepare : ∀ zero, aspis_core.field.wide_exact.WideExact.ZERO base=ok zero →
   first D pub proof hash none (Array.repeat 29#usize zero)=
   verifier.candidate.prepare (children base expected) D pub proof hash none (Array.repeat 29#usize zero))
 (query_loop : ∀ c, Reaches base expected D pub public_bytes proof k hash c →
   base.op7 proof c.prepared c.accumulator c.scratch none c.geometry c.pending k=
   expected.op7 proof c.prepared c.accumulator c.scratch none c.geometry c.pending k)
 (checkpoint : ∀ c a pending, Reaches base expected D pub public_bytes proof k hash c →
   expected.op7 proof c.prepared c.accumulator c.scratch none c.geometry c.pending k=ok (.Ok (a,pending)) →
   ∀ cells, base.op17 pending (alloc.vec.Vec.deref_mut a.weights).1=ok cells →
   base.op16 D c.prepared {a with weights:=(alloc.vec.Vec.deref_mut a.weights).2 cells} proof public_bytes hash=
   expected.op16 D c.prepared {a with weights:=(alloc.vec.Vec.deref_mut a.weights).2 cells} proof public_bytes hash) :
 NHL_EmittedTx1.tx1 base first D pub public_bytes proof k hash none=
 verifier.candidate.tx1 (children base expected) D pub public_bytes proof k hash none := by
 rw [←NHL_Tx1Eq.source (children base expected),NHL_Tx1Stages.factor,NHL_Tx1Stages.factor]
 unfold run
 rw [before_children,before_prepare base first _ D pub public_bytes proof k hash none prepare]
 apply NHL_BindOn.reached
 intro reply prior
 cases reply with
 | Err e => rfl
 | Ok c =>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
   unfold queryCut
   have reached : Reaches base expected D pub public_bytes proof k hash c := prior
   change (do
     let r ← base.op7 proof c.prepared c.accumulator c.scratch none c.geometry c.pending k
     let cf ← core.result.Result.Insts.CoreOpsTry.branch r
     match cf with
     | .Continue pair => afterQuery base D public_bytes proof hash none c.prepared pair.1 pair.2
     | .Break residual =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual)=_
   rw [query_loop c reached]
   apply NHL_BindOn.reached
   intro queryReply queryCall
   cases queryReply with
   | Err e => rfl
   | Ok pair =>
     rcases pair with ⟨a,pending⟩
     simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
     unfold afterQuery
     simp only [lift,bind_tc_ok,children]
     apply NHL_BindOn.reached
     intro cells finishCall
     rw [checkpoint c a pending reached queryCall cells finishCall]
#print axioms source
end AspisR1.NHL_Tx1Model
