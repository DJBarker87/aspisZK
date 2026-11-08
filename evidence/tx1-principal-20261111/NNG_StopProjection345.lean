import NNG_Pure345
set_option autoImplicit false
namespace AspisR1.NNG_StopProjection345
open RSL NNG_Obs345 NNG_Pure345

theorem reject {A : Type} (e : ProgramError) (next : Unit → Obs (Except ProgramError A)) :
 tryObs (check true e) next=silent (.error e) := rfl
#print axioms reject
end AspisR1.NNG_StopProjection345
