import XRq_SamplerInterface
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace XRq_LeafErrors

theorem ordinary_fail (e : Error) (block : Array U8 32#usize) :
 XRq_SamplerInterface.ordinary (fun _ => fail e) block = fail e := rfl

theorem ordinary_div (block : Array U8 32#usize) :
 XRq_SamplerInterface.ordinary (fun _ => div) block = div := rfl

theorem gamma_fail (e : Error) (block : Array U8 32#usize) :
 XRq_SamplerInterface.gamma (fun _ => fail e) block = fail e := rfl

theorem gamma_div (block : Array U8 32#usize) :
 XRq_SamplerInterface.gamma (fun _ => div) block = div := rfl
#print axioms ordinary_fail
#print axioms ordinary_div
#print axioms gamma_fail
#print axioms gamma_div
end XRq_LeafErrors
