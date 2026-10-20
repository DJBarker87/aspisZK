import CuSavingsLibraReferencePowers
import OccupancyRangeTraversal
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraReferenceLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Libra
open CuSavingsLibraSourceModel CuSavingsLibraSourceControl OccupancyRangeTraversal
open CuSavingsLibraReferencePowers (Powers Extra)
variable {R S : Type} [CommSemiring R] [CommSemiring S] [Shared]
variable (A : Arithmetic R S)
abbrev Low := Array E 16#usize
abbrev Tables := Array Powers 2#usize
abbrev State := Range × E

def partialSum (f : Nat → R) (n : Nat) : R := ((List.range n).map f).sum

theorem partialSum_succ (f : Nat → R) (n : Nat) : partialSum f (n+1)=partialSum f n+f n := by
  simp only [partialSum,List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]

def term (low : Low) (extra : Extra) (j s : Nat) : R :=
  if 16*j+s<56 then
    A.decodeE (lookup low field.wide_exact.WideExact.ZERO s) *
      A.embedding ((A.decodeK (lookup extra field.QM31.ONE ((16*j+s)/28)))^((16*j+s)%28))
  else 0

def block (low : Low) (extra : Extra) (j : Nat) : R := partialSum (term A low extra j) 16

def body (low : Low) (powers : Tables) (j : Usize) : State → Result (ControlFlow State E)
  | (iter,acc) =>
    old.twofold_libra_weights.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop.body
      low powers j iter acc

private theorem source_index (j s : Usize) (hj : j.val<4) (hs : s.val<16) :
    ∃ base index,
      (16#usize*j : Result Usize)=.ok base ∧ (base+s : Result Usize)=.ok index ∧
      index.val=16*j.val+s.val := by
  obtain ⟨base,hbase,hbaseV⟩ := WP.spec_imp_exists
    (UScalar.mul_spec (x:=16#usize) (y:=j) (by scalar_tac))
  have hb : base.val=16*j.val := by simpa only [UScalar.ofNatCore_val_eq] using hbaseV
  obtain ⟨index,hindex,hindexV⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=base) (y:=s) (by scalar_tac))
  exact ⟨base,index,hbase,hindex,by simpa only [hb] using hindexV⟩

theorem source_success (low : Low) (powers : Tables) (extra : Extra) (j : Usize)
    (hj : j.val<4)
    (hlow : ∀ s, s<16 → A.canonicalE (lookup low field.wide_exact.WideExact.ZERO s))
    (hpowers : CuSavingsLibraReferencePowers.Valid A powers extra) :
    ∃ value,
      old.twofold_libra_weights.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop
        {start:=0#usize,«end»:=16#usize} low powers j field.wide_exact.WideExact.ZERO=.ok value ∧
      A.canonicalE value ∧ A.decodeE value=block A low extra j.val := by
  let I : State → Prop := fun state =>
    state.1.«end»=16#usize ∧ state.1.start.val≤16 ∧ A.canonicalE state.2 ∧
      A.decodeE state.2=partialSum (term A low extra j.val) state.1.start.val
  let Q : E → Prop := fun value => A.canonicalE value ∧ A.decodeE value=block A low extra j.val
  have step : ∀ state, I state → state.1.start.val<16 →
      ∃ next, body low powers j state=.ok (.cont next) ∧ I next ∧ next.1.start.val=state.1.start.val+1 := by
    intro state hs hi
    rcases state with ⟨iter,acc⟩
    change iter.«end»=16#usize ∧ iter.start.val≤16 ∧ A.canonicalE acc ∧
      A.decodeE acc=partialSum (term A low extra j.val) iter.start.val at hs
    rcases hs with ⟨hend,hstart,hacc,hvalue⟩
    change iter.start.val<16 at hi
    have hit : iter.start.val < iter.«end».val := by rw [hend];simpa using hi
    obtain ⟨iter1,hnext,hiter1,hend1,_⟩ := next_step iter hit
    obtain ⟨base,index,hbase,hindex,hindexV⟩ := source_index j iter.start hj hi
    by_cases hactive : 16*j.val+iter.start.val<56
    · have hilt : index<56#usize := by change index.val<(56#usize).val;scalar_tac
      obtain ⟨side,hside,hsideV⟩ := UScalar.div_spec index (y:=28#usize) (by scalar_tac)
      obtain ⟨exponent,hexponent,hexponentV⟩ := WP.spec_imp_exists (UScalar.rem_spec index (y:=28#usize) (by scalar_tac))
      have hsV : side.val=(16*j.val+iter.start.val)/28 := by simpa only [UScalar.ofNatCore_val_eq,hindexV] using hsideV
      have heV : exponent.val=(16*j.val+iter.start.val)%28 := by simpa only [UScalar.ofNatCore_val_eq,hindexV] using hexponentV
      have hsb : side.val<2 := by omega
      have heb : exponent.val<28 := by omega
      have hlread := read low field.wide_exact.WideExact.ZERO iter.start (by simpa using hi)
      have htread := read powers (Array.repeat 28#usize field.QM31.ONE) side (by simpa using hsb)
      have hqread := read (lookup powers (Array.repeat 28#usize field.QM31.ONE) side.val) field.QM31.ONE exponent (by simpa using heb)
      obtain ⟨hpc,hpv⟩ := hpowers side.val hsb exponent.val heb
      obtain ⟨product,hproduct,hproductC,hproductV⟩ := A.mixed
        (lookup low field.wide_exact.WideExact.ZERO iter.start.val)
        (lookup (lookup powers (Array.repeat 28#usize field.QM31.ONE) side.val) field.QM31.ONE exponent.val)
        (hlow iter.start.val hi) hpc
      obtain ⟨sum,hsum,hsumC,hsumV⟩ := A.add acc product hacc hproductC
      refine ⟨(iter1,sum),?_,?_,hiter1⟩
      · unfold body old.twofold_libra_weights.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop.body
        dsimp only
        rw [hnext]
        simp only [bind_tc_ok]
        dsimp only
        rw [hbase]
        simp only [bind_tc_ok]
        dsimp only
        rw [hindex]
        simp only [bind_tc_ok]
        dsimp only
        simp only [hilt,if_pos]
        rw [hlread]
        simp only [bind_tc_ok]
        dsimp only
        rw [hside]
        simp only [bind_tc_ok]
        dsimp only
        rw [hexponent]
        simp only [bind_tc_ok]
        dsimp only
        rw [htread]
        simp only [bind_tc_ok]
        dsimp only
        rw [hqread]
        simp only [bind_tc_ok]
        dsimp only
        rw [hproduct]
        simp only [bind_tc_ok]
        dsimp only
        rw [hsum]
        rfl
      · change iter1.«end»=16#usize ∧ iter1.start.val≤16 ∧ A.canonicalE sum ∧
          A.decodeE sum=partialSum (term A low extra j.val) iter1.start.val
        refine ⟨hend1.trans hend,by omega,hsumC,?_⟩
        rw [hiter1,partialSum_succ,hsumV,hvalue,hproductV,hpv]
        simp only [term,hactive,if_pos,hsV,heV]
    · have hinactive : ¬index<56#usize := by change ¬index.val<(56#usize).val;scalar_tac
      refine ⟨(iter1,acc),?_,?_,hiter1⟩
      · unfold body old.twofold_libra_weights.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop.body
        dsimp only
        rw [hnext]
        simp only [bind_tc_ok]
        dsimp only
        rw [hbase]
        simp only [bind_tc_ok]
        dsimp only
        rw [hindex]
        simp only [bind_tc_ok]
        dsimp only
        simp only [hinactive,if_false]
      · change iter1.«end»=16#usize ∧ iter1.start.val≤16 ∧ A.canonicalE acc ∧
          A.decodeE acc=partialSum (term A low extra j.val) iter1.start.val
        refine ⟨hend1.trans hend,by omega,hacc,?_⟩
        rw [hiter1,partialSum_succ,hvalue]
        simp only [term,hactive,if_false,add_zero]
  have done : ∀ state, I state → state.1.start.val=16 →
      ∃ value, body low powers j state=.ok (.done value) ∧ Q value := by
    intro state hs hi
    rcases state with ⟨iter,acc⟩
    change iter.«end»=16#usize ∧ iter.start.val≤16 ∧ A.canonicalE acc ∧
      A.decodeE acc=partialSum (term A low extra j.val) iter.start.val at hs
    rcases hs with ⟨hend,_,hacc,hvalue⟩
    change iter.start.val=16 at hi
    have hd := next_done iter (by rw [hend];simpa using (show iter.start.val≥16 by omega))
    refine ⟨acc,?_,hacc,?_⟩
    · unfold body old.twofold_libra_weights.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop.body
      dsimp only
      rw [hd]
      rfl
    · simpa only [block,hi] using hvalue
  have initial : I ({start:=0#usize,«end»:=16#usize},field.wide_exact.WideExact.ZERO) :=
    ⟨rfl,by scalar_tac,A.zero,by simpa only [show (0#usize).val=0 by scalar_tac,partialSum,List.range_zero,List.map_nil,List.sum_nil] using A.zero_value⟩
  obtain ⟨value,hloop,hcanonical,hdecode⟩ := execute_invariant (body low powers j)
    (fun state : State => state.1.start.val) I Q 16 step done _ initial (by scalar_tac)
  refine ⟨value,?_,hcanonical,hdecode⟩
  unfold old.twofold_libra_weights.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop
  exact hloop

#print axioms source_success
end AspisR1.CuSavingsLibraReferenceLoop
