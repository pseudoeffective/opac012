# OPAC-012 working notes

## Conventions (checked against Lewis–Morales arXiv:1707.08192 and the OPAC blog)
- Paper: I_w := {(i, w_j) : i<j, w_i<w_j} (NON-inversion diagram); blog: Rothe diagram of the 321-avoiding w_0 w. Same boards.
- M_r(B,q) = m_r(B,q)/(q-1)^r, reduced count of rank-r matrices with support in B.
- For v = (2n-1)(2n)(2n-3)(2n-2)...12: I_v = {(2j-1, 2n-2j+2)} = n cells in distinct rows/cols.
  Complement = 2n x 2n square minus n "rook" cells. Checked: n=1 gives q, n=2 at q=2 gives 4416 = q^4 S_2(2). OK.
- Family for Conj 6.9: 123-avoiding w with I_w = k isolated cells  <=>  w = w_0 s_{i_1}...s_{i_k}, |i_a-i_b|>=2 (so m>=2k).
  (Rothe diagram of u=w_0 w has no two cells in a row/col iff inversion graph of u is a matching iff u is a product of disjoint adjacent transpositions.)

## Reformulation
S_{k,m}(q) = sum_i (-1)^i C(k,i) [m-i]!  =  [m-k]! * F_k(m-k),
F_0(a)=1,  F_{t+1}(a) = [a+1] F_t(a+1) - F_t(a).
At q=1: F_t(a) = # injections [t] -> [t+a] with no fixed point.
Empirically S_{k,m} in N[q]  <=>  m >= 2k-1 (k>=3); i.e. F_t(a) in N[q] iff a >= t-1. Conjecture is a = t.

Small: F_1(a)=q[a];  F_2(a) = q[a+1] F_1(a) + q^{a+1} F_0(a).
Classical (q=1): F_k(r) = (r+k-1) F_{k-1}(r) + (k-1) F_{k-2}(r).   <-- look for q-analogue.

## Matrix side (verified by brute force, t<=3)
#(t x N full-rank matrices over F_q, zeros at (i,i), i<=t) = (q-1)^t q^{C(t-1,2)-1} F_t(N-t).
Row-by-row count gives exactly the recurrence F_{t+1}(a)=[a+1]F_t(a+1)-F_t(a); the minus sign comes from
the case "column t of the first t-1 rows is zero" (then the last row has fewer choices). Positive bookkeeping
attempts (tracking nonzero free columns) produce (q-1)^{|Z|-1} factors -> not termwise positive.

## Low-degree structure
F_t(a) == q^t/(1-q)^t  (mod q^{a+1});  next correction -q^{a+1}(q^t-(2q-1)^t)/(1-q)^{t+1} (mod q^{2a+2}).
=> coefficient of q^{a+1} is (-1)^t and of q^{a+2} is 1-t when a<=t-2: explains threshold a>=t-1.

## Involution (sequences over N u {*}, bounds a+rank-1, toggle first 0/*):
F_t(a) = q^t [a][a+1]...[a+t-1] + sum_{l=1}^{t-1} q^{l-1}[a]...[a+l-2] (F_{t-l}(a+l)-F_{t-l}(a+l-1)).
Unmatched objects: a 0 followed by a suffix containing a coordinate at its max.

## Failed: code statistics (any order/direction, any placement) do not realize F_t(a) for t>=3;
falling/rising/q-binomial bases in a all have negative coefficients; no clean 3-term recurrence in t.

## Idea under test: S_{k,m} = Euler char of the complex A -> (+)A/x_j -> (+)A/(x_j,x_j') -> ...,
A = coinvariant algebra of S_m (Hilb A/(x_I) = [m-|I|]!). If exact beyond H^0 then S_{k,m}=Hilb(cap_j x_j A) >= 0.
RESULT: complex exact only for k<=2. For k=3: Hilb(cap x_j A_m) - S_{3,m} = q^{m-2}[m-2]!  (m=4,5,6). Dead end for positivity.

## KEY DECOMPOSITION (found 2026-09-08)
mu_t(a) := q^t [a-t+1][a+1][a+2]...[a+t-1].   F_t(a) = mu_t(a) + q^{a+1} T_t(a),  T_t(a) >= 0 observed for a>=t-1, t<=6.
Recurrence (proved by direct computation of [a+1]mu_t(a+1)-mu_t(a)-mu_{t+1}(a) = q^{a+1} Pi_t(a) ([2t-1]+[a+t])):
   T_1 = 0,  T_{t+1}(a) = Pi_t(a)([2t-1]+[a+t]) + q[a+1] T_t(a+1) - T_t(a),  Pi_t(a) = [a+1]...[a+t-1].
   T_2 = 1+[a+1].   T_3 = (2q+q^2)[a+1] + [2][a+1][a+2] - 1.
Threshold a>=t-1 is exactly where [a-t+1] >= 0.

## Algebraic framework (2026-09-09)
Pi_k(a) = [a+1]...[a+k],  beta_k(a) = [a][a+1]...[a+k-1].  Lemma A: Pi_k = sum_{j<=k} q^j [k]!/[j]! beta_j  (from [a+k+1]=[k+1]+q^{k+1}[a]).
beta_k = q^{-k}(Pi_k - [k] Pi_{k-1}).
L'' g(a) := q[a+1] g(a+1) - g(a);   L'' Pi_k = q Pi_{k+1} - Pi_k.   T_{t+1} = sigma_t + L'' T_t,  sigma_t = [2t-1] Pi_{t-1} + Pi_t.
=> T_t = sum_{s=1}^{t-1} (qS-1)^{t-1-s} sigma_s  (S = shift on Pi-basis).  Pi-coefficients g_k^{(t)} alternate.
Observed: T_t = sum_j theta_{t,j} beta_j with theta_{t,j} in N[q] (t<=5).  theta_{t,j} = q^j/[j]! * Theta_{t,j},  Theta_{t,j} = sum_{k>=j} [k]! g_k^{(t)}.
Theta_{t,0} = T_t(0) = S_{t,t}/q + [t-1][t-1]!.   Theta_{t,t-1} = [t-1][t-1]!.
Recurrence: Theta_{t+1,j} = [t-1]!([2t-1]+[t]) 1_{j<=t-1} + [t]! 1_{j=t} + q[j]Theta_{t,j-1} + (q^{j+1}-1)Theta_{t,j} + sum_{k>j} q^{k+1} Theta_{t,k}.
GOAL: prove Theta_{t,j} >= 0 (then F_t(a) = mu_t(a) + q^{a+1} sum_j theta_{t,j} beta_j(a) >= 0 for a >= t-1).

## Explicit formula (verified t<=8) and reduction
N=t-1, E_0=[N]![N], E_d=q^{N-d}[N-d]! lambda_d, lambda_d=sum_{s=d}^N C(s,d) q^{N-s}.
Theta_{t,j} = E_0 + sum_{d=1}^{N-j} (-1)^{d+1} E_d.   (Pi-coeffs: g_{t-1}=[t-1], g_k=(-1)^{t-k} q^k gamma_k, gamma_k=lambda_{N-k}.)
KEY LEMMA (numerically true N<=11): E_0 >= sum_{even d>=2} E_d coefficientwise.  => all Theta_{t,j}>=0 => theorem.

## PROOF OF KEY LEMMA (2026-09-09) -- via Lambda^{(d)} := (E_0 - sum_{i<=d} E_i)/[N-d]!
Lambda^{(0)}=[N];  Lambda^{(d)} = [N-d+1] Lambda^{(d-1)} - q^{N-d} lambda_d.
Claim: Lambda^{(d)} = P_d + q^{N-d+1} Q_d,  P_d = sum_{k<N-d} C(k+d,d) q^k (truncated (1-q)^{-d-1}),  Q_d in N[q].
Induction: [N-d+1]P_{d-1} - q^{N-d}lambda_d = sum_{n<N-d} C(n+d,d) q^n + sum_{u=0}^{N-d} c_u q^{N-d+u},
  c_u = C(N,d) - C(u+d-1,d) - C(N-u,d) >= 0 by convexity of x->C(x,d) (max at endpoints u=0: 0, u=N-d: C(N-1,d-1)-1>=0).
Hence Q_d = sum_{u>=1} c_u q^{u-1} + q[N-d+1]Q_{d-1} >= 0.  => R_N = Lambda^{(N)} >= 0, and E_0 - sum_{i<=d}E_i >= 0 for all d.
Then Theta_{t,j} = [j]! Lambda^{(N-j)} + 2 sum_{odd d<=N-j} E_d >= 0.
FINAL: F_t(a) = q^t [a-t+1] prod_{i=1}^{t-1}[a+i] + q^{a+1} sum_j q^j binom(a+j-1,j)_q Theta_{t,j}.   (beta_j/[j]! = qbinom)
Sharpness: F_t(a) == q^t/(1-q)^t - q^{a+1}(q^t-(2q-1)^t)/(1-q)^{t+1} mod q^{2a+3}: coefficient of q^{a+1} is C(a,t-1)+(-1)^t, of q^{a+2} is C(a+1,t-1)-(t-1).
Matrix identity (self-contained): M_m(complement of k isolated cells) = q^{C(m,2)-k} S_{k,m}, from last-row recursion + free rows.
