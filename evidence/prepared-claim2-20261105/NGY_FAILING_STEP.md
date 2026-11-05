# Failed steps retained

Prelaunch generation: selected frozen line offset was one line too late; generator assertion rejected it. Corrected to exact source lines59-60. No compiler launched for that input. NGY_K001 admission was obtained before the missing-payload exception, then reused only as a filename for the actual later launch; exactly one capped NGY_K001 exists.

K001: excluded before Kani; inherited source inventory included removed NGU_stages.rs. Own generator now removes that obsolete harness pin and adds only NGY inputs. The frozen release inventory remains checked.

K002: Kani compiler rejected inclusion of the exact KMX stubs without allocator_api. Scratch lib now adds only cfg_attr(kani,feature(allocator_api)), recorded in NGY_HARNESS.patch. No shipped file changed. No timeout or memory kill.

K003: all-points joined inner_iteration reached CBMC and timed out at90s, 3,785,828KiB peak RSS, swap0. No pass and no unchanged rerun. Replacement splits the point sum into six source-case harnesses; all pre/poststate fields and both replies remain arbitrary.

Own statement review after K008: the initial Out encoded the exhaustive source Result as a Parse Boolean and control but did not retain Result<(),Error> as a field. Its narrower record contracts remain valid and are superseded for final native association by an added full Result field. No false Rust counterexample; no native full-Result closure credit assigned to the earlier schema. Queue held before further cases; strengthened outputs require new source/config attempts, not unchanged replays.

K014: strengthened full-Result point2, arbitrary lane0..28, CBMC TIMEOUT90s, wall97.578s, peak1,853,364KiB, swap0. Excluded. Queue stops before K015 from its obsolete plan. Replacement retains point_2 name and splits the quantified lane into lower/upper intervals, both full-state and both Result arms; paired controls are newly scoped. No timeout/cap increase or unchanged rerun.
