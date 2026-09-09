"""Independent numerical check of the identities in opac012-positivity.tex (sympy).

F_t(a) = sum_i (-1)^{t-i} C(t,i) [a+1]...[a+i]          (S_{k,m} = [m-k]! F_k(m-k))
Theorem 2.2:  F_t(a) = q^t [a-t+1] prod_{i=1}^{t-1}[a+i] + q^{a+1} sum_j q^j qbinom(a+j-1,j) Theta_{t,j}
with Theta_{t,j} = E_0 + sum_{d=1}^{N-j} (-1)^{d+1} E_d,  N=t-1, E_0=[N]![N], E_d = q^{N-d}[N-d]! lambda_{N,d},
lambda_{N,d} = sum_{s=d}^N C(s,d) q^{N-s}.
Key Lemma: Lambda^{(D)} := [N-D+1] Lambda^{(D-1)} - q^{N-D} lambda_{N,D}, Lambda^{(0)}=[N], satisfies
   Lambda^{(D)} = P_D + q^{N-D+1} Q_D,  P_D = sum_{n<N-D} C(n+D,D) q^n,  Q_D in N[q].
"""
import sympy as sp
q = sp.symbols('q')

def qint(n):            # [n]_q for n >= 0
    return sum(q**i for i in range(n))
def qfact(n):
    r = sp.Integer(1)
    for i in range(1, n+1): r *= qint(i)
    return sp.expand(r)
def qbinom(n, k):
    if k < 0 or n < k: return sp.Integer(0)
    return sp.cancel(qfact(n)/(qfact(k)*qfact(n-k)))
def Pi(k, a):           # [a+1]...[a+k], a >= 0
    r = sp.Integer(1)
    for i in range(1, k+1): r *= qint(a+i)
    return sp.expand(r)
def F(t, a):
    return sp.expand(sum((-1)**(t-i)*sp.binomial(t, i)*Pi(i, a) for i in range(t+1)))
def S(k, m):
    return sp.expand(sum((-1)**i*sp.binomial(k, i)*qfact(m-i) for i in range(k+1)))
def lam(N, d):
    return sum(sp.binomial(s, d)*q**(N-s) for s in range(d, N+1))
def E(N, d):
    return sp.expand(q**(N-d)*qfact(N-d)*lam(N, d))
def Lam(N, D):
    L = qint(N)
    for i in range(1, D+1):
        L = sp.expand(qint(N-i+1)*L - q**(N-i)*lam(N, i))
    return L
def Theta(t, j):
    N = t-1
    return sp.expand(qfact(N)*qint(N) + sum((-1)**(d+1)*E(N, d) for d in range(1, N-j+1)))
def F_formula(t, a):
    mu = q**t*qint(a-t+1)
    for i in range(1, t): mu *= qint(a+i)
    return sp.expand(mu + q**(a+1)*sum(q**j*qbinom(a+j-1, j)*Theta(t, j) for j in range(t)))
def coeffs(P):
    P = sp.expand(P)
    return [0] if P == 0 else sp.Poly(P, q).all_coeffs()[::-1]

if __name__ == "__main__":
    ok = True
    for t in range(1, 8):
        for a in range(t-1, t+4):
            if sp.expand(F_formula(t, a) - F(t, a)) != 0: ok = False; print("Thm 2.2 fails", t, a)
    print("Theorem 2.2 formula agrees with F_t(a), t<=7:", ok)
    ok = True
    for N in range(1, 11):
        for D in range(0, N+1):
            cs = coeffs(Lam(N, D))
            P = [sp.binomial(n+D, D) for n in range(N-D)]
            if any(cs[n] != P[n] for n in range(N-D)) or (N-D < len(cs) and cs[N-D] != 0) or min(cs) < 0:
                ok = False; print("Key Lemma fails", N, D)
            if sp.expand(qfact(N-D)*Lam(N, D) - (qfact(N)*qint(N) - sum(E(N, d) for d in range(1, D+1)))) != 0:
                ok = False; print("Lambda identity fails", N, D)
    print("Key Lemma (structure + positivity), N<=10:", ok)
    ok = True
    for t in range(1, 10):
        for j in range(t):
            if min(coeffs(Theta(t, j))) < 0: ok = False; print("Theta negative", t, j)
    print("Theta_{t,j} >= 0, t<=9:", ok)
    ok = True
    for k in range(1, 8):
        for m in range(k, 2*k+3):
            pos = min(coeffs(S(k, m))) >= 0
            expected = (m >= 2*k-1) or k <= 2
            if pos != expected: ok = False; print("threshold fails", k, m)
    print("S_{k,m} in N[q] iff m>=2k-1 (or k<=2), k<=7:", ok)
