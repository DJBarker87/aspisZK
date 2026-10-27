import R1Z.ProverRw21Arity16Loop
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21Arity16NoPole
open Aeneas Aeneas.Std Result ProverRwFull ProverRw21Arity16Endpoint
variable [ExternalTypes]

theorem no_pole (ops : ExternalFuns) (f g : Compression) (h : Agree16 f g) :
    @host_semantic.no_pole _ {ops with op223 := f} =
      @host_semantic.no_pole _ {ops with op223 := g} := by
  funext compiled lambda chi
  simp only [host_semantic.no_pole,ProverRw21Arity16Loop.rows ops f g h]
  rfl

theorem closure (ops : ExternalFuns) (f g : Compression) (h : Agree16 f g)
    {H T : Type} (D : aspis_core.digest.Digest32 H) (C : host_semantic.Commitments T) :
    @host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error.call_once
        _ {ops with op223 := f} H T D C =
      @host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error.call_once
        _ {ops with op223 := g} H T D C := by
  funext c args
  simp only [host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error.call_once,
    no_pole ops f g h]
  rfl

theorem closure_dictionary (ops : ExternalFuns) (f g : Compression) (h : Agree16 f g)
    {H T : Type} (D : aspis_core.digest.Digest32 H) (C : host_semantic.Commitments T) :
    @host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error
        _ {ops with op223 := f} H T D C =
      @host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error
        _ {ops with op223 := g} H T D C := by
  simp only [host_semantic.build_with_material.closure.Insts.CoreOpsFunctionFnOncePairQM31QM31ResultVecQM31Error,
    closure ops f g h]

#print axioms no_pole
#print axioms closure
#print axioms closure_dictionary
end R1Z.ProverRw21Arity16NoPole
