# Resume 4 running tally

Baseline ff8096896d; 23/73 candidate source rows, endpoint removals0.
Env-J assigned38300–38599; next unused38304. Lean4/100 charged:
38300 stopped full-dictionary reduction143 (time log incomplete);
38301 CompressSupport PASS;38302 stopped selected-dictionary reduction143;
38303 isolated Op223Boundary PASS. No accepted source row added.
Reserve the final3 compile attempts for joint axioms audit.

Kani:1/12 used (circle gate timed out in CBMC, compiler passed);
compress16 gate currently running, charge on invocation completion.
Configuration diagnosis:1/3 probes used, trivial PASS, historical ICE not
reproduced on trivial harness. Mitigation only within own directory: four-core
CPU affinity; same caps/jobs/timeouts. Exact details in KANI-CONFIG.md.
