import NEW_GeometryActual.Funs
set_option autoImplicit false
namespace NEW_GeometryFixtures
open Aeneas Aeneas.Std Result

def queries : Array U32 22#usize := Array.make 22#usize
 [0#u32,1#u32,2#u32,3#u32,4#u32,5#u32,6#u32,7#u32,8#u32,9#u32,10#u32,
  11#u32,12#u32,13#u32,14#u32,15#u32,16#u32,17#u32,18#u32,19#u32,20#u32,21#u32]
def invalid : Array U32 22#usize := Array.make 22#usize
 [0#u32,1#u32,2#u32,3#u32,4#u32,5#u32,6#u32,262144#u32,8#u32,9#u32,10#u32,
  11#u32,12#u32,13#u32,14#u32,15#u32,16#u32,17#u32,18#u32,19#u32,20#u32,21#u32]

def packed (q : Array U32 22#usize) (lo hi : Usize) : Lean.Json :=
 match NEW_GeometryActual.verifier.QueryGeometry.for_range q lo hi with
 | .ok (.Ok g) => Lean.Json.mkObj [
    ("start",Lean.toJson g.start.val),
    ("inverses",Lean.toJson (g.inverses.val.map (fun r => r.val.map (fun x => x.val)))),
    ("line_z",Lean.toJson (g.line_z.val.map (fun x => x.val)))]
 | .ok (.Err .Query) => .str "Query"
 | .ok (.Err _) => .str "other-error"
 | .fail .assertionFailure => .str "assertionFailure"
 | .fail _ => .str "other-failure"
 | .div => .str "div"

def fixtures : List (String × Lean.Json) := [
 ("tx1",packed queries 0#usize 10#usize),
 ("tx2",packed queries 10#usize 22#usize),
 ("all",packed queries 0#usize 22#usize),
 ("empty",packed queries 7#usize 7#usize),
 ("bad_start",packed queries 11#usize 10#usize),
 ("bad_end",packed queries 0#usize 23#usize),
 ("bad_query",packed invalid 0#usize 10#usize)]
#eval (Lean.Json.mkObj fixtures).compress
#print axioms NEW_GeometryActual.verifier.QueryGeometry.for_range
end NEW_GeometryFixtures
