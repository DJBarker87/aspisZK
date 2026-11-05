import NIG_PairTail
import NIG_PairInputs
set_option autoImplicit false
noncomputable section
namespace NIG_PairValues
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem slice_read {T:Type} (P:T→Prop) (xs:Slice T) (i:Usize) (x:T)
 (all:∀ y∈xs.val,P y) (run:Slice.index_usize xs i=ok x):P x:=by
 unfold Slice.index_usize at run
 split at run
 · cases run
 · cases Result.ok.inj run
   exact all _ (List.getElem_mem _)

theorem powers4 (x:NE) (h:canonE x) (powers:Array NE 4#usize)
 (run:FIo_Native.weights.powers 4#usize x=ok powers):∀ p∈powers.val,canonE p:=by
 obtain ⟨expected,source,model,canonical⟩:=NFW_PowersCohort.source 4#usize x h
 cases Result.ok.inj (source.symm.trans run)
 exact canonical

theorem power_inputs (proof:Slice U8) (v:AspisR1Stage2.verifier.View)
 (p:AspisR1Stage2.verifier.Prepared) (a:AspisR1Stage2.verifier.Accumulator)
 (domain:NIG_FinishInput.Domain proof v p a) (i:Usize) (x:NE)
 (run:Slice.index_usize (FIo_Install.toSlice p.alpha.to_slice) i=ok x):canonE x:=
 slice_read canonE _ i x (NIG_PairInputs.alphas proof v p a domain) run

#print axioms slice_read
#print axioms powers4
#print axioms power_inputs
end NIG_PairValues
