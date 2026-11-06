Owned client/config/seed scripts copied from NKQ with prefix, workspace, budget and seed inputs changed. Admission, transport, disk and cgroup validation unchanged. No infrastructure changes.

Native gate strengthened: compare every inherited scratch source against committed NKQ pins, allowing only the two explicit NLC cfg(kani) module suffixes. The mandatory baseline input is uploaded by the owned client. Gate/source checks and dependency-lock validation remain mandatory. K001 source pins will also be compared against this baseline read-only; no native shape is rerun.

Final export is restricted to the checked loaded closure. Unloaded diagnostic/inspector objects remain in the retained workspace but are not exported as coherent proof inputs. Both predecessor comparisons remain mandatory.
