import R1Z.PV_CBL_CallbackBundle
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_BundleFrame
open ProverRwFull
set_option autoImplicit false

/-- Publication changes no allocator callback, so the deferred allocation
result is retained verbatim, including its error and returned vector. -/
theorem reserve (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_CallbackBundle.Types base)) :
    @ExternalFuns.op32 _ (PV_CBL_CallbackBundle.selectedAll base ops) =
      @ExternalFuns.op32 _ ops := rfl

theorem pop (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_CallbackBundle.Types base)) :
    @ExternalFuns.op33 _ (PV_CBL_CallbackBundle.selectedAll base ops) =
      @ExternalFuns.op33 _ ops := rfl

theorem array (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_CallbackBundle.Types base)) :
    @ExternalFuns.op36 _ (PV_CBL_CallbackBundle.selectedAll base ops) =
      @ExternalFuns.op36 _ ops := rfl

theorem sha_update (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_CallbackBundle.Types base)) :
    @ExternalFuns.op208 _ (PV_CBL_CallbackBundle.selectedAll base ops) =
      @ExternalFuns.op208 _ ops := rfl

theorem join (base : ExternalTypes)
    (ops : @ExternalFuns (PV_CBL_CallbackBundle.Types base)) :
    @ExternalFuns.op26 _ (PV_CBL_CallbackBundle.selectedAll base ops) =
      @ExternalFuns.op26 _ ops := rfl
#print axioms reserve
#print axioms pop
#print axioms array
#print axioms sha_update
#print axioms join
end R1Z.PV_CBL_BundleFrame
