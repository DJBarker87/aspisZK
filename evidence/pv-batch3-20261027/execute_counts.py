from run import H,run
import sys
# This execution records counts and bytes, never a whole-prover timing metric.
sys.exit(run('fixture-counts-'+sys.argv[1],['timeout','300',str(H/'bin/pv_b3_counts'),str(H/('fixture-count-output-'+sys.argv[1])),'0','1'],'optimized proof generation and P_R1 certificate elimination for transfer and withdrawal; counts/bytes only'))
