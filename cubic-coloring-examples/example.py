"""Check the same finite colorings as the Lean examples."""
from itertools import product

def valid(neighbors, colors):
    return all(colors[v] not in {colors[u] for u in N} and
               len({colors[u] for u in N}) == 2 for v, N in enumerate(neighbors))
K33 = [{3,4,5}]*3 + [{0,1,2}]*3
assert valid(K33, [0,0,1,2,2,3])
assert not any(valid(K33, c) for c in product(range(3), repeat=6))
H = [{7,8,9},{7,10,11},{7,12,13},{8,10,12},{8,11,13},{9,10,13},{9,11,12},
     {0,1,2},{0,3,4},{0,5,6},{1,3,5},{1,4,6},{2,3,6},{2,4,5}]
assert valid(H, [0,0,2,0,2,1,0,1,1,2,2,1,1,0])
lines = H[7:]
assert not any(all(len({c[v] for v in L}) == 2 for L in lines)
               for c in product(range(2), repeat=7))
print('K33: four colors work; three do not. Heawood: three colors work.')
print('Fano plane: no property-B coloring.')
