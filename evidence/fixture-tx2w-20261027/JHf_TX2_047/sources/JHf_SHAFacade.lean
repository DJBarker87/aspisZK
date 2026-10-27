module
public import JFn_HashBoundary
public import JFp_SHADigest
import JGz_Realizes
public section
namespace AspisR1.JHf_SHAFacade
/-- Single module-system trial: the SHA proof dependency is a private import;
only the exact named realization statement is exported. No new trust item. -/
theorem source : JFn_HashBoundary.Realizes JFp_SHADigest.digest := JGz_Realizes.source
#print axioms source
end AspisR1.JHf_SHAFacade
