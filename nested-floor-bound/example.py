"""Evaluate both nested floors using exact integer square roots."""
from math import isqrt
for n in range(1, 21):
    m = isqrt(2*n*n)
    a = m + isqrt(2*m*m)
    k = m+2*n-a
    assert m*m < 2*n*n < (m+1)*(m+1)
    assert k in (1, 2)
    print(f'n={n:2d} a(n)={a:3d}; error = {k} + fractional_part(sqrt(2)*{n})')
