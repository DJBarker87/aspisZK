from run import H,run
import sys
which,suffix=sys.argv[1:];assert which in ['base','candidate']
sys.exit(run('fixture-bytes-run-'+which+'-'+suffix,['timeout','300',str(H/('bin/pv_b3_bytes_'+which)),str(H/('fixture-bytes-output-'+which+'-'+suffix)),'0','1'],'optimized transfer/withdrawal proof generation and P_R1 elimination; fixture-byte comparison only, no whole-prover timing metric'))
