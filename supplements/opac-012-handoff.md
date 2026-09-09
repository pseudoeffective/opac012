# Handoff: OPAC-011 / OPAC-012 — $q$-rook positivity for matrices over $\mathbb{F}_q$

## The targets

For a board $B \subseteq [n]\times[n]$ let $M_n(B,q)$ denote the number of invertible $n\times n$ matrices over $\mathbb{F}_q$ whose support is contained in $B$. For $w\in\mathfrak{S}_n$ write $I_w$ for the inversion (Rothe) diagram of $w$ and $\overline{I_w}$ for its complement. **Confirm the exact normalization conventions from §6 of Lewis–Morales before starting**; the blog restatement is lossy.

**Conjecture (Lewis–Morales, Conj. 6.8 = OPAC-012).** For $v = (2n-1)(2n)(2n-3)(2n-2)\cdots 3412 \in \mathfrak{S}_{2n}$ one has

$$M_{2n}(\overline{I_v},q) \;=\; q^{2n(n-1)} \sum_{i=0}^{n} (-1)^i \binom{n}{i} [2n-i]!_q,$$

and this lies in $\mathbb{N}[q]$. Equivalently, since the prefactor is a monomial, the task is

$$S_n(q) \;:=\; \sum_{i=0}^{n} (-1)^i \binom{n}{i}\,[2n-i]!_q \;\in\; \mathbb{N}[q],
\qquad [k]!_q = \prod_{j=1}^{k}(1+q+\cdots+q^{j-1}).$$

Verified computationally for $n \le 40$.

**Conjecture (Lewis–Morales, Conj. 6.9 = OPAC-011).** For every $123$-avoiding $w \in \mathfrak{S}_n$, $M_n(\overline{I_w},q) \in \mathbb{N}[q]$.

Note: the OPAC blog PDF renders the pattern as $1324$; the source paper says $123$-avoiding, and by Billey–Jockusch–Stanley these are exactly the permutations whose diagrams are skew Ferrers boards. Use the skew-shape formulation.

## What is already known

Haglund (1998) proved the Ferrers-board case: $M_n(B,q)$ is, up to a power of $q-1$, a polynomial in $q$ with nonnegative coefficients, tied to the Garsia–Remmel $q$-rook numbers. Lewis–Morales proved polynomiality with integer coefficients for all Rothe diagrams, and exhibited permutations where coefficients go negative — so the $123$-avoiding hypothesis is doing real work. Skew Ferrers boards are the natural first extension beyond Haglund.

## Suggested lines of attack

1. **Combinatorial interpretation of $S_n(q)$.** At $q=1$, $S_n(1) = \sum_i (-1)^i\binom{n}{i}(2n-i)!$ is an inclusion–exclusion count of permutations of $[2n]$ avoiding $n$ specified disjoint positions. Find the right statistic ($\mathrm{inv}$ or $\mathrm{maj}$ flavored) making $S_n(q)$ the generating function over that set, i.e. produce a sign-reversing involution on the signed set that cancels the negative terms and leaves a statistic-preserving residue. Dworkin's interpretation of the Garsia–Remmel $q$-hit numbers is the model to imitate.
2. **Recursion.** Look for a recurrence in $n$ for $S_n(q)$ whose coefficients are manifestly in $\mathbb{N}[q]$; the $q$-Pascal structure of $[2n-i]!_q$ makes this plausible.
3. **Skew shapes by induction (for Conj. 6.9).** Push Haglund's argument from Ferrers to skew Ferrers by peeling rows/columns. Attack restricted subfamilies first: skew shapes with at most two rows, hooks plus a Ferrers piece, staircase-like shapes. Each such subfamily is an infinite family and is a reportable result on its own.

## Success criterion and working style

A run is worth reporting only if it yields at least one **proven** infinite family: a full proof of Conj. 6.8, or Conj. 6.9 for an infinite subclass of $123$-avoiding permutations. Small-$n$ computation is for guessing statistics and testing candidate involutions, not for extending the verified range — $n \le 40$ is already checked and more data adds nothing.

## References

- J.B. Lewis, A.H. Morales, *Rook theory of the finite general linear group*, <https://arxiv.org/abs/1707.08192> (Conjectures 6.8, 6.9; §6.3 for the explicit formula).
- A. Klein, J.B. Lewis, A.H. Morales, *Counting matrices over finite fields with support on skew Young diagrams and complements of Rothe diagrams*, <https://arxiv.org/abs/1203.5804>.
- J.B. Lewis, A.H. Morales, *Combinatorics of diagrams of permutations*, <https://arxiv.org/abs/1405.1608>.
- J. Haglund, *$q$-rook polynomials and matrices over finite fields*, Adv. Appl. Math. **20** (1998), 450–487.
- A.M. Garsia, J.B. Remmel, *$q$-counting rook configurations and a formula of Frobenius*, JCTA **41** (1986), 246–275.
