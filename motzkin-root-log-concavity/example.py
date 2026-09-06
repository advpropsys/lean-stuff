"""Compute finite sequence values; Lean proves the all-index and sharpness results."""
M = [1, 1]
for n in range(1, 20):
    numerator = (2*n+3)*M[n] + 3*n*M[n-1]
    assert numerator % (n+3) == 0
    M.append(numerator // (n+3))
T = [1]
for n in range(1, len(M)):
    T.append(M[n]-T[n-1])
def delta(n):
    return T[n]**(2*(n*n-1)) - T[n-1]**(n*(n+1))*T[n+1]**(n*(n-1))
assert delta(5) < 0
assert all(delta(n) > 0 for n in range(6, 20))
print('T[0:13] =', T[:13])
print('Strict reverse at center 5; strict log-concavity at centers 6 through 19.')
