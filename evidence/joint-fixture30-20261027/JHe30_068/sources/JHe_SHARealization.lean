import JHe_SHAEquations0
import JHe_SHAEquations1
import JHe_SHAEquations2
set_option autoImplicit false
namespace AspisR1
/-- Exactly453 concrete batch SHA equations, partitioned to keep record elaboration bounded. -/
class JHe_SHARealization : Prop where
  tree0 : JHe_SHA0
  tree1 : JHe_SHA1
  tree2 : JHe_SHA2
instance [s : JHe_SHARealization] : JHe_SHA0 := s.tree0
instance [s : JHe_SHARealization] : JHe_SHA1 := s.tree1
instance [s : JHe_SHARealization] : JHe_SHA2 := s.tree2
end AspisR1
