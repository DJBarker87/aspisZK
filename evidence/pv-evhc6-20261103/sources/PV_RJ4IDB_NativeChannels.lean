import PV_RJ4IDB_NativeTrace
set_option autoImplicit false
namespace PV_RJ4IDB

theorem nativeFiles_translation (es : List NativeEvent) :
 files (es.map translateEvent) = nativeFiles es := by
 induction es with
 | nil => rfl
 | cons e es ih =>
   simp only [files,nativeFiles] at ih
   cases e <;> simp only [List.map_cons,files,nativeFiles,List.filterMap_cons,translateEvent,ih]
#print axioms nativeFiles_translation

theorem nativeJSON_translation (es : List NativeEvent) :
 json (es.map translateEvent) = nativeJSON es := by
 induction es with
 | nil => rfl
 | cons e es ih =>
   simp only [json,nativeJSON] at ih
   cases e <;> simp only [List.map_cons,json,nativeJSON,List.filterMap_cons,translateEvent,ih]
#print axioms nativeJSON_translation

theorem nativeStdout_translation (es : List NativeEvent) :
 stdout (es.map translateEvent) = nativeStdout es := by
 induction es with
 | nil => rfl
 | cons e es ih =>
   simp only [stdout,nativeStdout] at ih
   cases e <;> simp only [List.map_cons,stdout,nativeStdout,List.filterMap_cons,translateEvent,ih]
#print axioms nativeStdout_translation

theorem nativeDiag2_translation (es : List NativeEvent) :
 diagnostics2 (es.map translateEvent) = nativeDiag2 es := by
 induction es with
 | nil => rfl
 | cons e es ih =>
   simp only [diagnostics2,nativeDiag2] at ih
   cases e <;> simp only [List.map_cons,diagnostics2,nativeDiag2,List.filterMap_cons,translateEvent,ih]
#print axioms nativeDiag2_translation

theorem nativeDiag3_translation (es : List NativeEvent) :
 diagnostics3 (es.map translateEvent) = nativeDiag3 es := by
 induction es with
 | nil => rfl
 | cons e es ih =>
   simp only [diagnostics3,nativeDiag3] at ih
   cases e <;> simp only [List.map_cons,diagnostics3,nativeDiag3,List.filterMap_cons,translateEvent,ih]
#print axioms nativeDiag3_translation

theorem nativeCounts_translation (es : List NativeEvent) :
 counts (es.map translateEvent) = nativeCounts es := by
 induction es with
 | nil => rfl
 | cons e es ih =>
   simp only [counts,nativeCounts] at ih
   cases e <;> simp only [List.map_cons,counts,nativeCounts,List.filterMap_cons,translateEvent,ih]
#print axioms nativeCounts_translation

theorem nativeTimes_translation (es : List NativeEvent) :
 times (es.map translateEvent) = nativeTimes es := by
 induction es with
 | nil => rfl
 | cons e es ih =>
   simp only [times,nativeTimes] at ih
   cases e <;> simp only [List.map_cons,times,nativeTimes,List.filterMap_cons,translateEvent,ih]
#print axioms nativeTimes_translation

theorem nativeOracle_translation (es : List NativeEvent) :
 oracle (es.map translateEvent) = nativeOracle es := by
 induction es with
 | nil => rfl
 | cons e es ih =>
   simp only [oracle,nativeOracle] at ih
   cases e <;> simp only [List.map_cons,oracle,nativeOracle,List.filterMap_cons,translateEvent,ih]
#print axioms nativeOracle_translation

theorem nativeRejections_translation (es : List NativeEvent) :
 rejections (es.map translateEvent) = nativeRejections es := by
 induction es with
 | nil => rfl
 | cons e es ih =>
   simp only [rejections,nativeRejections] at ih
   cases e <;> simp only [List.map_cons,rejections,nativeRejections,List.filterMap_cons,translateEvent,ih]
#print axioms nativeRejections_translation

theorem nativeSide_translation (es : List NativeEvent) :
 sideChannels (es.map translateEvent) = nativeSide es := by
 induction es with
 | nil => rfl
 | cons e es ih =>
   simp only [sideChannels,nativeSide] at ih
   cases e <;> simp only [List.map_cons,sideChannels,nativeSide,List.filterMap_cons,translateEvent,ih]
#print axioms nativeSide_translation
end PV_RJ4IDB
