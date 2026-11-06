import Aeneas
import AdapterRwModel
run_elab do
  let env ← Lean.getEnv
  for (n, _) in env.constants.toList do
    let s := n.toString
    if (s.startsWith "Aeneas.Std" && (s.contains "RefCell" || s.contains "RefMut" || s.contains "Clock" || s.contains "Pubkey")) then
      Lean.logInfo m!"{n}"
#print AdapterRw.observer
