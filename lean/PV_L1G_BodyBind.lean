import R1Z.PV_W_Threading
set_option autoImplicit false
namespace PV_L1G_BodyBind
open R1Z.PV_W_Threading
variable {W C E A B : Type}
/-- Full leaf equality only at the actually returned value and post-world;
all earlier calls and failure worlds are retained by composition. -/
theorem bind_at (m m' : M W C E A) (k k' : A → M W C E B) (w : W)
 (first : m w = m' w)
 (next : ∀ a, (m w).outcome = .ok a → k a (m w).world = k' a (m w).world) :
 R1Z.PV_W_Threading.bind m k w = R1Z.PV_W_Threading.bind m' k' w := by
 cases h : (m w).outcome with
 | fail e => simp only [R1Z.PV_W_Threading.bind,← first,h]
 | div => simp only [R1Z.PV_W_Threading.bind,← first,h]
 | ok a => simp only [R1Z.PV_W_Threading.bind,← first,h,next a h]
#print axioms bind_at
end PV_L1G_BodyBind
