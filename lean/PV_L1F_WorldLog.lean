import PV_L1D_Logged
import R1Z.PV_OWN_WorldAdapter
set_option autoImplicit false
namespace PV_L1F_WorldLog
open Aeneas Aeneas.Std
open R1Z.PV_W_Threading
open PV_L1D_Logged
abbrev Event := R1Z.SideChannelL1AttemptRecord.Event
/-- Forget only pre-world annotations in this auxiliary L1 log. The original
Run remains available; its terminal and post-world are never replaced. -/
def result {E A : Type} (error : E → Aeneas.Std.Error) : Outcome E A → Result A
 | .ok a => .ok a
 | .fail e => .fail (error e)
 | .div => .div

def log {W E A : Type} (error : E → Aeneas.Std.Error) (r : Run W Event E A) : Logged A :=
 ⟨r.calls.map Prod.snd,result error r.outcome⟩

theorem bind_log {W E A B : Type} (error : E → Aeneas.Std.Error)
 (m : M W Event E A) (k : A → M W Event E B) (w : W) :
 log error (R1Z.PV_W_Threading.bind m k w) =
 PV_L1D_Logged.bind (log error (m w)) (fun a => log error (k a (m w).world)) := by
 cases h : (m w).outcome with
 | fail e => simp only [R1Z.PV_W_Threading.bind,h,log,result,PV_L1D_Logged.bind]
 | div => simp only [R1Z.PV_W_Threading.bind,h,log,result,PV_L1D_Logged.bind]
 | ok a => simp only [R1Z.PV_W_Threading.bind,h,log,result,PV_L1D_Logged.bind,List.map_append]
#print axioms bind_log

theorem fail_world {W E A B : Type} (m : M W Event E A) (k : A → M W Event E B)
 (w : W) (e : E) (h : (m w).outcome=.fail e) :
 (R1Z.PV_W_Threading.bind m k w).world=(m w).world ∧
 (R1Z.PV_W_Threading.bind m k w).calls=(m w).calls := by
 rw [R1Z.PV_W_Threading.bind_fail m k w e h]
 exact ⟨rfl,rfl⟩
#print axioms fail_world

theorem div_world {W E A B : Type} (m : M W Event E A) (k : A → M W Event E B)
 (w : W) (h : (m w).outcome=.div) :
 (R1Z.PV_W_Threading.bind m k w).world=(m w).world ∧
 (R1Z.PV_W_Threading.bind m k w).calls=(m w).calls := by
 rw [R1Z.PV_W_Threading.bind_div m k w h]
 exact ⟨rfl,rfl⟩
#print axioms div_world
end PV_L1F_WorldLog
