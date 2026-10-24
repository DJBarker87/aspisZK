import Lean
open Lean
#eval show IO Unit from do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Port17RELEASE_Control}, {module := `Port6AUTH_Accounting}] {}
  let roots := #[`AspisR1.Port17RELEASE_Control.rust, `AspisR1.Port17RELEASE_Invariant.tx1,
    `AspisR1.Port17RELEASE_Invariant.tx2, `AspisR1.Port6AUTH_Accounting.first_reads,
    `AspisR1.Port1_Driver.rust, `AspisR1.Port1_Driver.stages,
    `AspisR1.VTop_Flow.tx1, `AspisR1.VTop_Flow.tx2_authenticated,
    `AspisR1.Port1_StoredCarrier.source]
  for root in roots do
    let mut pending := [root]
    let mut seen : Std.HashSet Name := {}
    let mut parent : Std.HashMap Name Name := {}
    while !pending.isEmpty do
      let n := pending.head!
      pending := pending.tail!
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.checked.get.find? n | throw (IO.userError s!"missing constant {n}")
      let mut ds := ci.type.getUsedConstants
      if let some v := ci.value? then ds := ds ++ v.getUsedConstants
      if let .inductInfo v := ci then ds := ds ++ v.ctors.toArray
      for d in ds do
        unless seen.contains d do
          unless parent.contains d do parent := parent.insert d n
          pending := d :: pending
      let origin := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!.toString)
      IO.println ("REACH " ++ (Json.arr #[toJson root.toString,toJson n.toString,toJson origin,
        toJson (parent[n]?.map Name.toString)]).compress)
    IO.println s!"REACH_COUNT {root} {seen.size}"
