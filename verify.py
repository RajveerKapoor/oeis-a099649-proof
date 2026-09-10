def S(n):
    return sum(int(d) ** 2 for d in str(n))

def orbit(n):
    seen, x = [], n
    while x not in seen:
        seen.append(x)
        x = S(x)
    return seen

terms = [n for n in range(1, 145) if max(orbit(n)) > n]
assert len(terms) == 130
assert terms[-1] == 144
assert max(orbit(144)) == 145
assert all(max(orbit(n)) <= n for n in range(145, 164))
assert all(S(n) < n for n in range(164, 1450))
print("verified: A099649 has 130 terms and final term 144")
