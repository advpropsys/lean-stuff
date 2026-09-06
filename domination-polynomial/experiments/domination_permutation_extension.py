"""Exact scalar certificate for an existential symmetric-permutation construction.
No permutation tuple is sampled, generated, or searched for by this script.
"""
import json
from fractions import Fraction as F
from pathlib import Path

b, d, w = 240000000000, 30000, 90
k, t = b//1500, 5*b
m_min, m_max = 3*b, b*(12*d+3)
L_min, L_max = w*m_min, w*m_max
n_max = t+L_max
K_min = t+L_min//2
floor_offset = (108*b)//125
epsilon, a, c, r = F(1,1500), F(2,25), F(57,1000), F(11,200)
entropy, eta = F(19,3000), F(1,15000)
soft, hard, noise = F(1,2**48), F(1,2**100), F(1,2**59)
noise_exponent = 2*r*r*b*b/L_max
# Offsets from K, so all comparisons hold for the unknown actual L as well.
ll, lh = -F(3407,3000)*b, -F(173,200)*b
rl, rh = -F(259,300)*b, -F(319,500)*b
projective_n = 44272117255374666459015
checks = {
    'b_multiple_1500': b%1500==0,
    'k_exact_epsilon_b': F(k,b)==epsilon,
    'e_above_27_over_10_via_series': F(65,24)>F(27,10),
    'log1500_below_8': 27**8>1500*10**8,
    'disperser_union_exponent_margin': F(d*k*k,b)-18*k==F(b,750),
    'disperser_margin_positive': F(b,750)>0,
    'log4500_below_17_over_2': 27**17>4500**2*10**17,
    'weighted_minority_entropy': epsilon*(1+F(17,2))==entropy,
    'left_tail_margin': a*a-entropy>=eta,
    'right_tail_margin': 2*c*c-entropy>=eta,
    'neutral_tail_margin': 1-2*entropy>=eta,
    'hard_exponent_above_110': eta*b>110,
    'hard_error': F(5,2**110)<hard,
    'soft_smallness': F(t,2**w)<F(1,2),
    'soft_error': F(2*t,2**w)<soft,
    'noise_exponent_above_42': noise_exponent>42,
    'noise_error': 2*F(10,27)**42<noise,
    'total_error_below_2_minus_47': soft+hard+noise<F(1,2**47),
    'phase_mass_above_one_third': (1-soft)*(F(1,2)-hard)*(1-noise)>F(1,3),
    'left_offsets_formula': (ll,lh)==(-(1+a+epsilon+r)*b,-(1-a-r)*b),
    'right_offsets_formula': (rl,rh)==(-(F(3,4)+c+2*epsilon+r)*b,-(F(3,4)-c-r)*b),
    'left_length': lh-ll==F(203,750)*b,
    'right_length': rh-rl==F(169,750)*b,
    'lengths_below_b': max(lh-ll,rh-rl)<b,
    'intervals_above_zero_for_all_actual_L': K_min+ll>0,
    'upper_offsets_negative': max(lh,rh)<0,
    'center_strict_gap': lh < -floor_offset < rl,
    'floor_left_integer_comparison': 200*floor_offset<173*b,
    'floor_right_integer_comparison': 300*floor_offset>259*b,
    'center_nonnegative_for_all_actual_L': K_min-floor_offset>=0,
    'w_even_so_every_actual_L_even': w%2==0,
    'b_plus_one_below_2_38': b+1<2**38,
    'pigeonhole_peak_above_2_minus_40': F(1,3*(b+1))>F(1,2**40),
    'strict_probability_valley': F(1,2**47)<F(1,2**40),
    'order_below_2_63': n_max<2**63,
    'order_strictly_smaller_than_projective': n_max<projective_n,
}
assert all(checks.values()), checks
record = {
    'scope':'Scalar existence certificate; no actual permutation tuple generated; canonical Lean construction unchanged',
    'b':b,'d':d,'w':w,'epsilon':str(epsilon),'k':k,'controls':t,
    'bipartite_degree_upper':2*d,'F_edges_lower':m_min,'F_edges_upper':m_max,
    'clone_count_lower':L_min,'clone_count_upper':L_max,'graph_order_upper':n_max,
    'union_bound_upper':'exp(-b/750) < 1',
    'noise_exponent_lower':str(noise_exponent),
    'left_interval_offsets_from_K':[str(ll),str(lh)],
    'right_interval_offsets_from_K':[str(rl),str(rh)],
    'center_offset_from_K':-floor_offset,
    'total_bad_probability_upper':'2^-47',
    'each_interval_probability_lower':'1/3',
    'peak_probability_lower':'2^-40',
    'previous_projective_order':projective_n,
    'guaranteed_integer_order_reduction':projective_n//n_max,
    'checks':checks,
}
output=Path(__file__).with_suffix('.json')
output.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'passed':len(checks),'order_upper':n_max,'reduction':record['guaranteed_integer_order_reduction']}))
