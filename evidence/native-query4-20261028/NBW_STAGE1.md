# KMX controls

K002–K007: six intended false assertions FAIL, one failing assertion per harness. K008–K013: six expected value controls PASS. All use the exact KMX_stubs.rs payload and frozen graph/lock, offline. No native query semantic claim is made by these controls. K001 is a compilation failure (Rust attribute recursion limit), excluded; scratch-only cfg(kani) recursion_limit=512 repairs it. Setup initially exceeded shell ARG_MAX before any Rust process; own setup transport now uses stdin. Kani budget charged conservatively:13/50.

NBW_controls_source.patch reconstructs the exact native module of K001–K013. The later NBW_harness.patch includes additional unexecuted targets. lib.rs differs in K001 only by absence of the later scratch-only recursion-limit attribute. No repository shipped source was edited; local frozen inventory has498 matches.
