# Serialization correction

NBO_L002 was mistakenly submitted before collecting terminal NBO_K001. This permits overlap and violates the one-scope rule; no result from this overlap is credited as a compliant run. L002 failed a lexical spacing error and is not accepted. K001 status is retained in its receipt, not suppressed. No shared infrastructure or another worker was touched.

Own build/run wrappers now take the same local advisory lock for their entire admission/submission/recovery lifetime. This strengthens the existing one-scope validation without modifying the shared launcher. No further compile is submitted until K001 is terminal. The corrected L002 source has changed and uses a new attempt number.

The first native setup failed before any metadata/Kani launch due to a quoted newline in the own sync script. It was repaired without changing validation. That prelaunch failure consumes no Kani attempt.
