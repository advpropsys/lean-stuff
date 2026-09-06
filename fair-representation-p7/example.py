"""Exhaust the 128 subsets; minimize each integer budget exactly."""
parts = [{2, 4, 6}, {1}, {3, 5, 7}]
independent = []
for mask in range(1 << 7):
    S = {i+1 for i in range(7) if mask >> i & 1}
    if any(i in S and i+1 in S for i in range(1, 7)):
        continue
    independent.append(S)
    lower = [(len(V)+1)//2-len(S & V) for V in parts]
    assert not (max(lower) <= 1 and sum(lower) <= 1)
assert [S for S in independent if len(S) >= 4] == [{1, 3, 5, 7}]
print(len(independent), 'independent subsets; none satisfies the integer-budget constraints.')
print('Unique size-four set:', [S for S in independent if len(S) == 4][0])
