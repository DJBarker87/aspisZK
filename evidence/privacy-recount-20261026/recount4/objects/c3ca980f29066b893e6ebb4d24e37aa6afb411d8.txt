# Timeout ruling correction

On re-reading pv-common.txt after context compaction, the worker found lead ruling (i), limiting a timed-out Kani retry to900s and requiring taskset CPUs0–3. Earlier invocation records truthfully preserve1800s settings and runs09/12 exceeded900s. This was a procedural error, not evidence of verification. Neither passed. No result is upgraded or hidden.

Run04 is already active with the older1800s setting. It will be stopped by900 elapsed seconds unless it terminates sooner. Future launches enforce <=900s and taskset0–3 in kani.py, keeping all checks, unwind assertions, optimized flags and memory caps. No infrastructure or production code is modified.
