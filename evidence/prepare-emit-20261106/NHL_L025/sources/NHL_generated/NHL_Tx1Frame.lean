import NHL_Tx1Stages
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_Tx1Model
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NHL_Tx1Stages

def children (base expected : Ops) : Ops :=
 {base with op7:=expected.op7,op16:=expected.op16}

theorem before_children (base expected : Ops) {H : Type} (prepareCall : NHL_EmittedTx1.Prepare H)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) :
 beforeQuery (children base expected) prepareCall D pub public_bytes proof k hash obs=
 beforeQuery base prepareCall D pub public_bytes proof k hash obs := by
 simp only [beforeQuery,children,compact.OFF_FOLDED_ROOT,compact.OFF_ROUND1,
   aspis_core.field.wide_exact.WideExact.ZERO]

/-- A prepare packet is required only at the actual initialized scratch,
including its complete rejection/post-scratch reply. -/
theorem before_prepare (base : Ops) {H : Type} (first second : NHL_EmittedTx1.Prepare H)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit))
 (prepare : ∀ zero, aspis_core.field.wide_exact.WideExact.ZERO base=ok zero →
   first D pub proof hash obs (Array.repeat 29#usize zero)=
   second D pub proof hash obs (Array.repeat 29#usize zero)) :
 beforeQuery base first D pub public_bytes proof k hash obs=
 beforeQuery base second D pub public_bytes proof k hash obs := by
 unfold beforeQuery
 split
 · rfl
 · apply NHL_BindOn.reached; intro shape shapeCall
   apply NHL_BindOn.reached; intro shapeControl shapeBranch
   cases shapeControl with
   | Break residual => rfl
   | Continue unit =>
     apply NHL_BindOn.reached; intro scan scanCall
     apply NHL_BindOn.reached; intro scanControl scanBranch
     cases scanControl with
     | Break residual => rfl
     | Continue unit =>
       apply NHL_BindOn.reached; intro marked markCall
       apply NHL_BindOn.reached; intro zero zeroCall
       rw [prepare zero zeroCall]
#print axioms before_children
#print axioms before_prepare
end AspisR1.NHL_Tx1Model
