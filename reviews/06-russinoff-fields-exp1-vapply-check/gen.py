# Independent reference: schoolbook polynomial multiplication and long division, coefficient lists
# constant term first. Writes ACL2 forms comparing the solution's vapply / pmod / pdivides with it.
import random, sys
from fractions import Fraction
random.seed(1)
out = []

def trim(a):
    a = list(a)
    while a and a[-1] == 0: a.pop()
    return a
def pmul(a, b, mod):
    r = [0] * (len(a) + len(b) - 1 if a and b else 0)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] = (r[i + j] + x * y) % mod if mod else r[i + j] + x * y
    return r
def prem(a, q, mod):            # remainder of a by monic q, by long division
    a = trim(a); n = len(q) - 1
    while len(a) > n:
        c = a[-1]; k = len(a) - 1 - n
        for i, qi in enumerate(q):
            a[k + i] = (a[k + i] - c * qi) % mod if mod else a[k + i] - c * qi
        a = trim(a)
    return a + [0] * (n - len(a))
def lit(x):
    if isinstance(x, Fraction):
        return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"
    return str(x)
def L(a): return "'(" + " ".join(lit(x) for x in a) + ")" if a else "nil"

cases = 0
for field in ['fp2', 'fp5', 'fp7', 'q']:
    mod = {'fp2': 2, 'fp5': 5, 'fp7': 7, 'q': None}[field]
    b = {'fp2': "'(:fp 2)", 'fp5': "'(:fp 5)", 'fp7': "'(:fp 7)", 'q': "'(:q)"}[field]
    rnd = (lambda: random.randrange(mod)) if mod else (lambda: Fraction(random.randint(-5, 5), random.randint(1, 3)))
    for _ in range(400):
        n = random.randint(1, 5)                       # deg p
        p = [rnd() for _ in range(n)] + [1]            # monic, length n+1
        a = [rnd() for _ in range(random.randint(0, 9))]
        v = [rnd() for _ in range(n)]                  # an element: exactly n coefficients
        exp_mul = prem(pmul(a, v, mod), p, mod)        # (a * v) mod p
        exp_mod = prem(a, p, mod)                      # a mod p
        divides = all(x == 0 for x in exp_mod)
        out.append(f"(cw \"C {field} ~x0~%\" (list (equal (vapply {b} {L(p)} {L(a)} {L(v)}) {L(exp_mul)}) "
                   f"(equal (pmod {b} {L(a)} {L(p)}) {L(exp_mod)}) (equal (pdivides {b} {L(p)} {L(a)}) {'t' if divides else 'nil'})))")
        cases += 1
    # divisibility positives: a = p * m for random m, so pdivides must be t
    for _ in range(100):
        n = random.randint(1, 4); p = [rnd() for _ in range(n)] + [1]
        m = [rnd() for _ in range(random.randint(1, 4))]
        a = pmul(p, m, mod)
        out.append(f"(cw \"C {field}-div ~x0~%\" (list (pdivides {b} {L(p)} {L(a)})))")
        cases += 1
open(sys.argv[1] if len(sys.argv) > 1 else 'cases.lsp', 'w').write("(set-guard-checking :none)\n" + "\n".join(out) + "\n")
print(cases, "cases")
