import JGl_NumericData
import JFu_PublicSemantic
import FIy_PublicDigest
set_option autoImplicit false
namespace AspisR1.JGl_DigestProbe
open Aeneas Aeneas.Std Result FIq_Native
#eval match pool_v1.pair_forest_semantic_terminal.public_digest_lanes
    JFu_PublicSemantic.value JGl_NumericData.openings JGl_NumericData.selectors with
  | .ok xs => String.intercalate ";" (xs.val.map (fun (q : field.QM31)=>
      toString q.c0.a.val ++ "," ++ toString q.c0.b.val ++ "," ++ toString q.c1.a.val ++ "," ++ toString q.c1.b.val))
  | _ => "failed"
end AspisR1.JGl_DigestProbe
