import NDO_JGr_Geometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_InstalledSlots
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller JGr_Geometry

theorem writer : @installed.op16 = @WAdm_Install.writer := rfl
#print axioms writer

theorem flush : installed.op17=Tx1Q_Install.flush := rfl
#print axioms flush

theorem query : installed.op7=Tx1Q_Install.query
    (Tx1Q_QueryBridge.leaves (SAQ_Decoder.install (JFr_TX2_DotsBinding.ops JGp_Seeds.query))) := rfl
#print axioms query

theorem initial : installed.op20=Tx1Q_PrefixInstall.initial true := rfl
#print axioms initial

theorem pending : installed.op18=Tx1Q_PrefixInstall.newPending true := rfl
#print axioms pending

theorem geometry : installed.op19=Tx1Q_PrefixInstall.geometryBody (SAQ_Constructor.install () JGp_Seeds.geometry) := rfl
#print axioms geometry
end AspisR1.JGw_InstalledSlots
end
