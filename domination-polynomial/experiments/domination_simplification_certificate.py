"""One improved member: exact scalar verification only, no graph search."""
import json
from fractions import Fraction as F
from math import isqrt
from pathlib import Path

q, w = 4194301, 100
b = q*q+q+1
t = 5*b
m = b*(6*q+9)
L = w*m
n = t+L
K = t+L//2
j = K-(108*b)//125
epsilon, a, c, r = F(1,1500), F(2,25), F(57,1000), F(11,200)
entropy = F(19,3000)
eta = F(1,15000)
noise_exponent = 2*r*r*b/F(w*(6*q+9))
soft, hard, noise = F(1,2**52), F(1,2**100), F(1,2**59)
left_lo, left_hi = K-F(3407,3000)*b, K-F(173,200)*b
right_lo, right_hi = K-F(259,300)*b, K-F(319,500)*b
checks = {
    "q_prime_all_divisors_through_sqrt": all(q%d for d in range(2,isqrt(q)+1)),
    "q_equals_2_22_minus_3": q == 2**22-3,
    "strict_disperser": q*1500**2 < (q+1)**2,
    "e_lower_helper": F(65,24)>F(27,10),
    "log4500_less_17_over_2_helper": 27**17 > 4500**2*10**17,
    "entropy_bound_identity": epsilon*(1+F(17,2)) == entropy,
    "left_tail_margin": a*a-entropy >= eta,
    "right_tail_margin": 2*c*c-entropy >= eta,
    "neutral_tail_margin_using_log4_ge_1": 1-2*entropy >= eta,
    "hard_exponent_above_110": eta*b > 110,
    "hard_bound_from_e_gt_2": F(5,2**110)<hard,
    "soft_smallness": F(t,2**w)<F(1,2),
    "soft_error_bound": F(2*t,2**w)<soft,
    "noise_exponent_above_42": noise_exponent > 42,
    "noise_error_bound_from_e_gt_2_7": 2*F(10,27)**42 < noise,
    "total_bad_below_2_minus_51": soft+hard+noise < F(1,2**51),
    "each_interval_mass_above_one_third": (1-soft)*(F(1,2)-hard)*(1-noise)>F(1,3),
    "gap_positive": a+c+2*epsilon+2*r < F(1,4),
    "left_endpoints_formula": (left_lo,left_hi)==(K-(1+a+epsilon+r)*b,K-(1-a-r)*b),
    "right_endpoints_formula": (right_lo,right_hi)==(K-(F(3,4)+c+2*epsilon+r)*b,K-(F(3,4)-c-r)*b),
    "left_interval_length": left_hi-left_lo == F(203,750)*b,
    "right_interval_length": right_hi-right_lo == F(169,750)*b,
    "interval_lengths_below_b": max(left_hi-left_lo,right_hi-right_lo)<b,
    "left_interval_inside_coefficient_range": 0<=left_lo<left_hi<=n,
    "right_interval_inside_coefficient_range": 0<=right_lo<right_hi<=n,
    "integer_center_strictly_in_gap": left_hi<j<right_lo,
    "floor_left_comparison": 200*((108*b)//125)<173*b,
    "floor_right_comparison": 300*((108*b)//125)>259*b,
    "center_valid": 0<=j<=n,
    "b_plus_one_at_most_2_44": b+1<=2**44,
    "pigeonhole_peak_above_2_minus_46": F(1,3*(b+1))>F(1,2**46),
    "strict_valley_probability_gap": F(1,2**51)<F(1,2**46),
    "L_even": L%2==0,
}
assert all(checks.values()), checks
data = {
    "scope":"Exact scalar inequalities for one smaller projective member; no graph enumeration and no canonical-file changes",
    "q":q,"w":w,"b":b,"t":t,"m":m,"L":L,"n":n,"K":K,"j":j,
    "epsilon":str(epsilon),"left_deviation":str(a),"right_deviation":str(c),
    "clone_deviation":str(r),"entropy_upper":str(entropy),"hard_exponent_rate":str(eta),
    "clone_exponent":str(noise_exponent),
    "left_interval":[str(left_lo),str(left_hi)],"right_interval":[str(right_lo),str(right_hi)],
    "trial_division_last_divisor":isqrt(q),"checks":checks,
    "original_n":15211807199220036387538871517957,
    "integer_reduction_factor":15211807199220036387538871517957//n,
}
out=Path(__file__).with_suffix('.json')
out.write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({"passed":len(checks),"n":n,"reduction_factor":data['integer_reduction_factor'],"output":str(out)}))
