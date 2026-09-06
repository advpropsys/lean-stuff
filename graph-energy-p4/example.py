"""Exact polynomial and squared-energy illustration."""
def mul(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out
# Ascending coefficients: (x^2-x-1)(x^2+x-1).
assert mul([-1,-1,1], [-1,1,1]) == [1,0,-3,0,1]
# Roots are ±(sqrt(5)+1)/2 and ±(sqrt(5)-1)/2.
energy_squared = 4*5
printed_lower_bound_squared = 2*3*4  # signed extreme magnitudes coincide
corrected_lower_bound_squared = 2*3*4 - (4*4//4)*1
assert energy_squared < printed_lower_bound_squared
assert energy_squared == corrected_lower_bound_squared
print('Characteristic polynomial: x^4 - 3*x^2 + 1')
print('Energy^2 =', energy_squared, '; printed bound^2 =', printed_lower_bound_squared)
print('Corrected bound^2 =', corrected_lower_bound_squared)
