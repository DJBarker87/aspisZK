import R1Z.PV_CBL_FallbackRoundComplete
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackRoundLanes
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar
set_option autoImplicit false
theorem lane0 (s : State) (w0 w1 u v : U32) :
    (do let r ← PV_CBL_FallbackRound.sha_fallback_reference.sha256_digest_round_x2
          (pack s.c s.d s.g s.h) (pack s.a s.b s.e s.f) (pack u v w1 w0)
        Array.index_usize r 0#usize) =
      ok ((step (step s w0) w1).a) := by
  rw [PV_CBL_FallbackRoundShape.shape]
  simp only [bind_tc_ok,index0]
#print axioms lane0
theorem lane1 (s : State) (w0 w1 u v : U32) :
    (do let r ← PV_CBL_FallbackRound.sha_fallback_reference.sha256_digest_round_x2
          (pack s.c s.d s.g s.h) (pack s.a s.b s.e s.f) (pack u v w1 w0)
        Array.index_usize r 1#usize) =
      ok ((step (step s w0) w1).b) := by
  rw [PV_CBL_FallbackRoundShape.shape]
  simp only [bind_tc_ok,index1]
#print axioms lane1
theorem lane2 (s : State) (w0 w1 u v : U32) :
    (do let r ← PV_CBL_FallbackRound.sha_fallback_reference.sha256_digest_round_x2
          (pack s.c s.d s.g s.h) (pack s.a s.b s.e s.f) (pack u v w1 w0)
        Array.index_usize r 2#usize) =
      ok ((step (step s w0) w1).e) := by
  rw [PV_CBL_FallbackRoundShape.shape]
  simp only [bind_tc_ok,index2]
#print axioms lane2
theorem lane3 (s : State) (w0 w1 u v : U32) :
    (do let r ← PV_CBL_FallbackRound.sha_fallback_reference.sha256_digest_round_x2
          (pack s.c s.d s.g s.h) (pack s.a s.b s.e s.f) (pack u v w1 w0)
        Array.index_usize r 3#usize) =
      ok ((step (step s w0) w1).f) := by
  rw [PV_CBL_FallbackRoundShape.shape]
  simp only [bind_tc_ok,index3]
#print axioms lane3
end R1Z.PV_CBL_FallbackRoundLanes
