import FJh_Native07RawWide
import FIw_CompositionOrigins
import FIw_OpeningCanonical
import FJa_BoxedCanonical
import FJa_PoseidonSelectors
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_PoseidonOnComposition
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FIw_CompositionOrigins (SemPub composition)
/-- Native07 VALUE from the SAME actual composition execution and boxed point.
This does not yet identify the complete composition value or literal family. -/
theorem value (pub : SemPub) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
    (lambda chi theta comp g h active : NQ) (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize)
    (hclaims : canonical claims) (hpoint : canonical point)
    (run : composition pub claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active))) :
    ∃ (a a1 a2 : Array NQ 16#usize) (s : pool_v1.pair_forest_copy_terminal.Selectors)
      (sops : state_only_poseidon.StateOnlyPoseidonSelectors) (poseidon : Array NQ 4#usize),
      c1=a ∧ pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s ∧
      pool_v1.pair_forest_semantic_terminal.poseidon_selectors s=ok sops ∧
      sops.local=s.low ∧ state_only_poseidon.evaluate_state_only_poseidon_oracle_projected
        ⟨a,a1,a2⟩ sops=ok poseidon ∧ canonical poseidon ∧
      decoded poseidon=FJh_Native07RawValue.model ⟨a,a1,a2⟩ sops ∧
      (fun j=>FIz_ConcretePack.embed (decoded poseidon j))=
        FJh_Native07RawWide.model ⟨a,a1,a2⟩ sops := by
  obtain ⟨a,a1,a2,s,sops,variant,semantic,poseidon,prepared,middle,copy,it,it1,
    same,r0,r1,r2,rs,rsp,rposeidon,rsem,rv,rc,rp,rit,rit1,rm,rf,ra⟩ :=
    FIw_CompositionOrigins.reached pub claims point lambda chi theta comp g h active c1 mask run
  have ca := FIw_OpeningCanonical.z claims a hclaims r0
  have ca1 := FIw_OpeningCanonical.succ claims a1 hclaims r1
  have ca2 := FIw_OpeningCanonical.xor12 claims a2 hclaims r2
  have cs := FJa_BoxedCanonical.value point s hpoint rs
  have sp := FJa_PoseidonSelectors.value s sops cs.1 cs.2 rsp
  have v := FJh_Native07RawValue.value ⟨a,a1,a2⟩ sops poseidon ca ca1 ca2 sp.2.1 sp.2.2.1 rposeidon
  have vw := FJh_Native07RawWide.value ⟨a,a1,a2⟩ sops poseidon ca ca1 ca2 sp.2.1 sp.2.2.1 rposeidon
  exact ⟨a,a1,a2,s,sops,poseidon,same,rs,rsp,sp.1,rposeidon,v.1,v.2,vw.2⟩
#print axioms value
end AspisR1.FJh_PoseidonOnComposition
end
