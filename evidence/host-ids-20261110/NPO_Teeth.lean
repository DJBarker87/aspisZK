import Lean
/-! NPO_ negative control for the leanchecker replay. Writes NPO_Teeth.olean (imports Init only)
containing one well-typed theorem and one ill-typed theorem `NPO_Teeth.bad : False := 0`, the latter
added with addDeclWithoutChecking. A replay that has teeth must reject this module. Nothing imports it. -/
open Lean
def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Init}] {} (loadExts := false)
  let mk (n : Name) (t v : Expr) : Declaration :=
    Declaration.thmDecl { name := n, levelParams := [], type := t, value := v, all := [n] }
  let good := mk `NPO_Teeth.good (mkConst ``True) (mkConst ``True.intro)
  let bad := mk `NPO_Teeth.bad (mkConst ``False) (mkNatLit 0)
  let k ← IO.ofExcept <| (env.toKernelEnv.addDeclCore 0 good none).mapError fun _ => IO.userError "good rejected"
  -- the kernel rejects `bad` when checked:
  match k.addDeclCore 0 bad none with
  | .ok _ => IO.println "UNEXPECTED: kernel accepted bad"; return 1
  | .error _ => IO.println "kernel rejects bad when checked (expected)"
  let k ← IO.ofExcept <| (Kernel.Environment.addDeclWithoutChecking k bad).mapError fun _ => IO.userError "unchecked add failed"
  let env' := (Environment.ofKernelEnv k).setMainModule `NPO_Teeth
  writeModule env' s!"{args[0]!}/NPO_Teeth.olean" (writeIR := false)
  IO.println "wrote NPO_Teeth.olean"
  return 0
