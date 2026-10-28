import JHe_SHARealization
import JHx_Tree0
import JHx_Tree1
import JHx_Tree2
set_option autoImplicit false
namespace AspisR1.JHx_Instance
#check JHe_SHARealization
theorem source : JHe_SHARealization := ⟨JHx_Tree0.source,JHx_Tree1.source,JHx_Tree2.source⟩
#print axioms source
instance realization : JHe_SHARealization := source
#print axioms realization
end AspisR1.JHx_Instance
