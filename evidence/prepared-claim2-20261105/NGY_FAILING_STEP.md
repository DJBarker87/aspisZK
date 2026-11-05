# Failed steps retained

Prelaunch generation: selected frozen line offset was one line too late; generator assertion rejected it. Corrected to exact source lines59-60. No compiler launched for that input. NGY_K001 admission was obtained before the missing-payload exception, then reused only as a filename for the actual later launch; exactly one capped NGY_K001 exists.

K001: excluded before Kani; inherited source inventory included removed NGU_stages.rs. Own generator now removes that obsolete harness pin and adds only NGY inputs. The frozen release inventory remains checked.

K002: Kani compiler rejected inclusion of the exact KMX stubs without allocator_api. Scratch lib now adds only cfg_attr(kani,feature(allocator_api)), recorded in NGY_HARNESS.patch. No shipped file changed. No timeout or memory kill.

K003: all-points joined inner_iteration reached CBMC and timed out at90s, 3,785,828KiB peak RSS, swap0. No pass and no unchanged rerun. Replacement splits the point sum into six source-case harnesses; all pre/poststate fields and both replies remain arbitrary.
