import FIv_HornerAlgebra
import FIv_CompositionOperands
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_CompositionExact
open Aeneas Aeneas.Std Result FIq_Native
open FIv_CompositionTrace (NQ SemPub composition)
open FIv_NativeValue (Canon decode K)

def polynomial (theta : K) (semantic : Array NQ 24#usize)
    (poseidon : Array NQ 4#usize) (copy : NQ) : K :=
  theta^28*decode copy+theta^4*FIv_HornerAlgebra.low theta semantic.val+
    FIv_HornerAlgebra.low theta poseidon.val

theorem value (pub : SemPub) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
    (lambda chi theta comp g h active : NQ) (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize)
    (success : composition pub claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active)))
    (ht : Canon theta) :
    ∃ (a a1 a2 : Array NQ 16#usize) (amount : Option U32)
      (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
      (sops : state_only_poseidon.StateOnlyPoseidonSelectors)
      (variant : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1)
      (semantic : Array NQ 24#usize) (poseidon : Array NQ 4#usize)
      (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1),
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok selectors ∧
      pool_v1.pair_forest_semantic_terminal.poseidon_selectors selectors=ok sops ∧
      state_only_poseidon.evaluate_state_only_poseidon_oracle_projected ⟨a,a1,a2⟩ sops=ok poseidon ∧
      pool_v1.pair_forest_semantic_terminal.semantic_packed {pub with withdrawal_amount:=amount}
        ⟨a,a1,a2⟩ selectors=ok semantic ∧
      pool_v1.pair_forest_semantic_terminal.copy_variant pub.variant=ok variant ∧
      pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h selectors lambda chi
        pub.transition.live_snapshot.next_pair_index variant=ok copy ∧
      copy.active=active ∧
      ((∀ x∈semantic.val,Canon x) → (∀ x∈poseidon.val,Canon x) → Canon copy.residual →
        Canon comp ∧ decode comp=polynomial (decode theta) semantic poseidon copy.residual) := by
  obtain ⟨a,a1,a2,amount,selectors,sops,variant,semantic,poseidon,prepared,middle,copy,iter,iter1,
    hsops,hselect,hposeidon,hsemantic,hvariant,hcopy,hprep,hi,hi1,hmid,hfinal,ha⟩ :=
    FIv_CompositionOperands.reached pub claims point lambda chi theta comp g h active c1 mask success
  have hp := FIv_PreparedNew.valid theta prepared ht hprep
  have it : iter=⟨semantic.val⟩ := by cases iter; cases hi; rfl
  have it1 : iter1=⟨poseidon.val⟩ := by cases iter1; cases hi1; rfl
  rw [it] at hmid
  rw [it1] at hfinal
  refine ⟨a,a1,a2,amount,selectors,sops,variant,semantic,poseidon,copy,
    hsops,hselect,hposeidon,hsemantic,hvariant,hcopy,ha,?_⟩
  intro hs hp4 hc
  have mid := FIv_Horner24.value semantic.val.reverse prepared theta copy.residual middle ht hc hp
    (fun x hx=>hs x (List.mem_reverse.mp hx)) (by simpa only [List.reverse_reverse] using hmid)
  have fin := FIv_Horner4.value poseidon.val.reverse prepared theta middle comp ht mid.1 hp
    (fun x hx=>hp4 x (List.mem_reverse.mp hx)) (by simpa only [List.reverse_reverse] using hfinal)
  refine ⟨fin.1,?_⟩
  rw [fin.2,mid.2,FIv_HornerAlgebra.four,FIv_HornerAlgebra.reversed]
  have len24 := semantic.property
  have len4 := poseidon.property
  change semantic.val.length=24 at len24
  change poseidon.val.length=4 at len4
  rw [len24,len4]
  unfold polynomial
  ring
#print axioms value
end AspisR1.FIv_CompositionExact
end
