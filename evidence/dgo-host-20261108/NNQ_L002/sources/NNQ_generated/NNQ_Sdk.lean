import NNQ_Split
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result

theorem sdk_withDigest {F C : Type} (c : DrvC_Installation.Configuration F C)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize)) :
    DrvC_Installation.sdk (withDigest c o) = {DrvC_Installation.sdk c with op43 := o} := rfl
#print axioms sdk_withDigest
end AspisR1.NNQ_HostDigest
end
