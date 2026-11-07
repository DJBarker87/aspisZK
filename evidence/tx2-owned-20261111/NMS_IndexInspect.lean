import NMS_RSLPoolCarriers
set_option pp.explicit true in
#print Aeneas.Std.Slice.index_usize
run_cmd do
 let env ← Lean.getEnv
 for (n,ci) in env.constants.toList do
  let s := n.toString
  if s.startsWith "Aeneas.Std.Slice" &&
     (s.toLower.contains "getelem" || s.contains "index_usize") then
   Lean.logInfo m!"{n}: {ci.type}"
