import NKY_LevelsStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_LevelsBody
open Aeneas Aeneas.Std Result ControlFlow
open NJX_AppendDomains (Frontier High)
open NJX_DigestCohort (O)
open NJX_AppendFold (State)
open NKY_LevelCarrier (Pair pair)

theorem source (index : U64) (f : Frontier) (o : O) (s : High)
 (before : State) (level : Usize) (hl : level.val<20) :
 NKY_LevelsLiteral.body NKY_LevelsLiteral.child index f o s (pair before).1 (pair before).2 level=
 (do let child ← NKI_LevelsFrame.call index f o s ⟨level.val,hl⟩
     let middle ← NJX_AppendFold.step before child
     let next ← level+1#usize
     ok (cont ((pair middle).1,(pair middle).2,next))) := by
 let i : Fin 20 := ⟨level.val,hl⟩
 let offset : Usize := UScalar.ofNatCore (34+level.val) (by scalar_tac)
 have hi : NJX_AppendDomains.level i=level := by apply UScalar.eq_of_val_eq;rfl
 have add : 34#usize+level=ok offset := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
 have rf : Array.index_usize f level=ok (NJX_AppendDomains.frontier f i) := by
  exact NJB_ArrayReads.read f level (by scalar_tac)
 have rs : Array.index_usize s offset=ok (NJX_AppendDomains.high s i) := by
  exact NJB_ArrayReads.read s offset (by dsimp [offset];scalar_tac)
 have hc : NKY_LevelsLiteral.child index level (NJX_AppendDomains.frontier f i) o (NJX_AppendDomains.high s i)=
  (do let out ← NKI_LevelsFrame.call index f o s i;ok (pair out)) := by
  simp only [NKY_LevelsLiteral.child,NKI_LevelsFrame.call,hi]
 rw [NKY_LevelsLiteral.body,if_pos (show level<20#usize from hl)]
 simp only [rf,add,rs,bind_tc_ok,hc,bind_assoc_eq]
 apply congrArg
 funext child
 exact NKY_LevelsStep.arithmetic before child level
#print axioms source
end AspisR1.NKY_LevelsBody
end
