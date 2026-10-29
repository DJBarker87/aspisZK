import NEF_InvSpecialisation
set_option autoImplicit false
namespace NEF
inductive Tag where | mul | add | inv | neg
  deriving DecidableEq
structure Event (B : Type) where
  tag : Tag
  left : B
  right : B
  deriving DecidableEq
structure Replies (B : Type) where
  aa : B
  bb : B
  norm : B
  invNorm : B
  a : B
  nb : B
  b : B

def expectedInvLog {B : Type} (zero : B) (x : CM B) (r : Replies B) : List (Event B) :=
  [⟨.mul,x.a,x.a⟩,⟨.mul,x.b,x.b⟩,⟨.add,r.aa,r.bb⟩,⟨.inv,r.norm,zero⟩,
   ⟨.mul,x.a,r.invNorm⟩,⟨.neg,x.b,zero⟩,⟨.mul,r.nb,r.invNorm⟩]

def logResult {B : Type} (r : Replies B) : CM B := ⟨r.a,r.b⟩
/-- Instantiating arbitrary call replies with the actual primitive meanings
recovers the source inverse, with the SAME seven call arguments in order. -/
theorem inverse_log_instantiation {B : Type} (mul add : B → B → B)
    (neg baseInv : B → B) (x : CM B) :
    let r : Replies B :=
      let aa := mul x.a x.a
      let bb := mul x.b x.b
      let norm := add aa bb
      let invNorm := baseInv norm
      ⟨aa,bb,norm,invNorm,mul x.a invNorm,neg x.b,mul (neg x.b) invNorm⟩
    logResult r = @invStatic B Id _ mul add neg baseInv x := rfl

/-- Exactly one inverse call, and the inverse input is the same norm. -/
theorem inverse_log_backend_argument {B : Type} (zero : B) (x : CM B) (r : Replies B) :
    (expectedInvLog zero x r)[3]? = some ⟨.inv,r.norm,zero⟩ := rfl
#print axioms inverse_log_instantiation
#print axioms inverse_log_backend_argument
end NEF
