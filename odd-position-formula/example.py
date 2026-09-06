"""Generate original breadth-first sequence and check the exact position formula."""
seen = [1, 2]
known = set(seen)
generation = list(seen)
for _ in range(11):
    nxt = []
    for x in generation:
        for y in (x+2, 2*x):
            if y not in known:
                known.add(y)
                seen.append(y)
                nxt.append(y)
    generation = nxt
fib = [0, 1]
for _ in range(12):
    fib.append(sum(fib[-2:]))
for n in range(1, 13):
    position = seen.index(2*n-1)+1
    assert position == n-1+fib[n+1]
    print(n, 2*n-1, position)
