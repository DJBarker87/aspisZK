import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4TowerAddV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1.TerminalV4TowerSub

open AspisR1.TerminalV4TowerAdd

theorem current_qm_sub_mod
    (x y : AspisR1SelectedMaskProbe.field.QM31)
    (hx : CanonicalQM x) (hy : CanonicalQM y) :
    ∃ z, AspisR1SelectedMaskProbe.field.QM31.sub x y = .ok z ∧
      CanonicalQM z ∧
      wordsQM z =
        (((x.c0.a.val + P - y.c0.a.val) % P,
          (x.c0.b.val + P - y.c0.b.val) % P),
         ((x.c1.a.val + P - y.c1.a.val) % P,
          (x.c1.b.val + P - y.c1.b.val) % P)) := by
  obtain ⟨a, ea, ca, va, vb⟩ := current_cm_sub_mod x.c0 y.c0 hx.1 hy.1
  obtain ⟨b, eb, cb, vc, vd⟩ := current_cm_sub_mod x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a, b⟩, ?_, ⟨ca, cb⟩, ?_⟩
  · simp only [AspisR1SelectedMaskProbe.field.QM31.sub, ea, eb,
      bind_tc_ok]
  · exact Prod.ext (Prod.ext va vb) (Prod.ext vc vd)

#print axioms current_qm_sub_mod
end AspisR1.TerminalV4TowerSub
