"""Exact illustrations of the universally proved polynomial obstruction."""
def Q(q):
    return 9*q**4-14*q**3-30*q*q-14*q+1
def H(q):
    return 13*q**6-30*q**5-78*q**4-94*q**3-78*q*q-30*q+1
assert Q(1) == -48 and H(1) == -296
for q in range(2, 21):
    assert Q(q) % q == H(q) % q == 1
for q in range(1, 5):
    print(q, Q(q), H(q))
print('For every integer q >= 2, each polynomial is 1 modulo q.')
