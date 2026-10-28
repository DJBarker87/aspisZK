import NDO_JGn_CompositionValue
import NDO_JGn_SelectedHelper
import NDO_JGn_TerminalArithmetic
import NDO_JGl_TerminalSuccess
import NDO_JGe_TerminalCondition
import NDO_JGe_Boundaries
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_TerminalIdentified
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)

theorem source {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H) :
    JGe_TerminalCondition.Identified := by
  obtain ⟨selected,a,b,c,m,s,sops,sem,pos,comp,g,h,copy,out,
    gather,hs,ha,hb,hc,hl,block,sel,ps,runpos,cpos,vpos,runsem,csem,vsem,runh,runcopy,
    runcomp,ccomp,cg,vcomp,run,cout,vout⟩ := JGl_TerminalSuccess.source D JGe_Boundaries.value hash
  have eh := JGn_SelectedHelper.value selected h gather runh
  rw [eh] at runcomp vout
  have cv := JGn_CompositionValue.value selected a m comp g copy.active hs gather runcomp
  have meaning : decode out=decode (FIq_Carriers.toQ JGd_NumericData.neededTerminal) := by
    rw [vout,cv.1,cv.2,JGn_TerminalArithmetic.composition]
    exact JGn_TerminalArithmetic.terminal
  have neededCanonical : Canon (FIq_Carriers.toQ JGd_NumericData.neededTerminal) :=
    JGd_NumericData.neededTerminal_canonical
  have same := JGb_DecodeInjective.source out (FIq_Carriers.toQ JGd_NumericData.neededTerminal)
    cout neededCanonical meaning
  rw [same] at run
  unfold JGe_TerminalCondition.Identified FIq_Terminal.terminal
  dsimp only [JFu_TerminalCallback.claims,JFu_TerminalPrefix.alpha,JFu_TerminalPrefix.challenges] at run
  rw [run,bind_tc_ok]
  rfl
#print axioms source

def shaDictionary : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit where
  coremarkerCopyInst := {cloneInst := {clone := fun x=>ok x}}
  digest := fun _ parts=>F3U_Oracle.hashv JFp_SHADigest.digest parts

theorem identified : JGe_TerminalCondition.Identified := source shaDictionary ()
#print axioms identified
end AspisR1.JGn_TerminalIdentified
end
