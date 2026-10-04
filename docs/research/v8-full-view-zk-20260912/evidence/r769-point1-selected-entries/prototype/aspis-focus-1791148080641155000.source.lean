import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R743JointSparseEntryBinding
import AspisV8R19.R760PointWeightPrototype
import AspisV8R19.R760PointWeightChunk06

/-! One fixed source-shaped point-1 entry from the saved selected 222-row
matrix.  The raw matrix is pinned in the accompanying receipt; this theorem
uses only the finite pointWeight expansions already checked in R748/R760. -/
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R760PointWeightPrototype
open AspisV8R19.R760PointWeightChunk06
noncomputable section
set_option autoImplicit false
namespace AspisV8R19.R769Point1SelectedEntry

abbrev M := ZMod 2147483647

/-- The densest selected R746 direction by the existing source-only leaf plan:
Lean `(d,s)=(127,2)`, corresponding to saved raw matrix column `(127,3)`.
The saved row `point_1` entry is the first M31 coordinate 2146454263. -/
theorem fixed_densest_point1_entry :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 127 2
      (.inr (.inl 1)) = 2146454263 := by
  unfold sparseObservation
  change (pw 511 - 7^(2+1)*pw 508) - (pw 3 - 7^(2+1)*pw 0) = 2146454263
  rw [pw_0511, pw_0508, pw3, pw0]
  decide

#print axioms fixed_densest_point1_entry
end AspisV8R19.R769Point1SelectedEntry
