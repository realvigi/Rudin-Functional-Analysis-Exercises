#import "template/pset.typ": *
#show: pset.with(title: "Chapter 7 — Fourier Transforms")

#let Sn = $cal(S)_n$

=
Using a change of variables we get
$
  hat(g)(t) &= integral_(RR^n) g e_(-t) dif m_n = integral_(RR^n) (f compose A) e_(-t) dif m_n \
  &= abs(det A)^(-1) integral_(RR^n) f dot (e_(-t) compose A^(-1)) dif m_n \
  &= abs(det A)^(-1) integral_(RR^n) f(x) e^(-i(t dot A^(-1) x)) dif m_n (x) \
  &= abs(det A)^(-1) integral_(RR^n) f(x) e^(-i((A^(-1))^* t) dot x) dif m_n (x) \
  &= abs(det A)^(-1) hat(f)((A^(-1))^* t)
$
and so we got $hat(g) = abs(det A)^(-1) hat(f) compose (A^(-1))^*$.

=
Put $Q(x) = 1 + |x|^2$, and for every $N$ put $p_N (f) = max_(|alpha| <= N) norm(Q^N D_alpha f)_oo$ and $V_N = {f in Sn : p_N (f) < N^(-1)}$.
Then ${V_N}$ is a local base for the topology of $Sn$.

Let $Phi : Sn -> Sn$ be the Fourier transform, and for every $N$ and every $f in Sn$ put $q_N (f) = sum_(j=0)^3 p_N (Phi^j f)$.
Note that $q_N$ is a seminorm on $Sn$, and satisfies $q_N (f) = q_N (hat(f))$ for every $f in Sn$.
Also, since the $p_N$ are continuous from $Sn$ to $RR$, and $Phi$ is continuous from $Sn$ to itself, we get that $q_N$ is continuous from $Sn$ to $RR$.

For every $N$ put $W_N = {f in Sn : q_N (f) < N^(-1)}$. Then $W_N$ is open.
Also $q_N (0) = 0$, and so $W_N$ is a neighborhood of $0$ in $Sn$ for every $N$.

#claim[${W_N}$ is a local base for the topology of $Sn$.] <wn-local-base>
#proof[
  In the first direction, from the definition of $q_N$ it is clear that $p_N (f) <= q_N (f)$ for every $f in Sn$, and so if $q_N (f) < N^(-1)$ then also $p_N (f) < N^(-1)$. Hence $W_N subset.eq V_N$ for every $N$.

  In the second direction, fix $N$; we need to show that there is some $k$ for which $V_k subset.eq W_N$.
  For $0 <= j <= 3$, the function $p_N compose Phi^j$ is a continuous map from $Sn$ to $[0, oo)$.
  So for every $0 <= j <= 3$ there is a neighborhood $U_j$ of $0$ in $Sn$ such that $p_N (Phi^j f) < (4N)^(-1)$ for every $f in U_j$.
  There is some $k$ for which $V_k subset.eq inter.big_(j=0)^3 U_j$. Then for every $f in V_k$ and every $0 <= j <= 3$ we have $p_N (Phi^j f) < (4N)^(-1)$.
  So for every $f in V_k$ we have $q_N (f) = sum_(j=0)^3 p_N (Phi^j f) < N^(-1)$, that is, $f in W_N$.
  So indeed $V_k subset.eq W_N$.
]

On the other hand, directly from the definition, ${W_N}$ is a local base for the topology that ${q_N}$ induces on $Sn$.
If two topologies on a vector space have a common local base, then they are identical.
So by @wn-local-base, ${q_N}$ induces the standard topology of $Sn$.

Let ${c_N}$ be a sequence of positive numbers such that $c_N -> 0$ as $N -> oo$. Put
$ d(f, g) = max_N (c_N q_N (f - g)) / (1 + q_N (f - g)). $
Then $d$ is a metric on $Sn$ which induces the same topology as the family of seminorms ${q_N}$, and so it induces the standard topology of $Sn$.
It is easy to see that $d$ is translation invariant. Also, for every $f, g$ we have
$
  d(hat(f), hat(g)) &= max_N (c_N q_N (hat(f) - hat(g))) / (1 + q_N (hat(f) - hat(g)))
  = max_N (c_N q_N (hat(f - g))) / (1 + q_N (hat(f - g))) \
  &= max_N (c_N q_N (f - g)) / (1 + q_N (f - g)) = d(f, g)
$
and so we found a metric $d$ on $Sn$ which induces the standard topology, is translation invariant, and with respect to which the Fourier transform is an isometry, as required.

= <ex-3>
+ We show that $f$ is not a tempered distribution.

  Let $psi in cal(D)(RR)$ such that $psi >= 0$ on all of $RR$, $psi = 0$ outside $(-1, 1)$ and $psi = 1$ on $(-1\/2, 1\/2)$.
  Let $alpha$ be a multi-index and $P$ a polynomial. Then for every $m$
  $
    norm(P dot D^alpha (e^(-m) (tau_m psi)))_oo &= e^(-m) norm(P dot tau_m D^alpha psi)_oo = e^(-m) max_(x in [m-1, m+1]) |P(x) D^alpha psi(x - m)| \
    &<= e^(-m) norm(D^alpha psi)_oo max_(x in [m-1, m+1]) |P(x)|
  $
  There is $t_0 > 0$ such that $|P|$ is increasing on $(t_0, oo)$, and so for every $m > t_0$ we get
  $
    norm(P dot D^alpha (e^(-m) (tau_m psi)))_oo <= e^(-m) norm(D^alpha psi)_oo max_(x in [m-1, m+1]) |P(x)| <= norm(D^alpha psi)_oo e^(-m) |P(m + 1)|
  $
  and of course $e^(-m) |P(m + 1)| stretch(->)_(m -> oo) 0$. Then $P dot D^alpha (e^(-m) (tau_m psi)) stretch(->)_(m -> oo) 0$ uniformly on $RR$, and so $e^(-m) tau_m psi stretch(->)_(m -> oo) 0$ in $Sn$.

  On the other hand, putting $psi_m = e^(-m) tau_m psi$, for every $m$ we have
  $
    integral_(-oo)^oo e^x psi_m (x) dif x = integral_(-oo)^oo e^(x - m) psi(x - m) dif x = integral_(-oo)^oo e^x psi(x) dif x >= integral_(-1\/2)^(1\/2) e^x dif x > 0
  $
  and in particular it is impossible that $integral_(-oo)^oo f psi_m dif m_n -> 0$ as $m -> oo$, and so $f$ cannot be extended to a continuous functional on $Sn$, that is, $f$ is not a tempered distribution, as required.

+ Put $h(x) = sin(e^x)$. Let $h'$ be the ordinary derivative of $h$, and $D h$ the distributional derivative of $h$.
  $h'$ is continuous, and so by integration by parts, for every $phi in cal(D)(RR)$ we have
  $ D h(phi) = - integral_RR h phi' dif m_n = integral_RR h' phi dif m_n $
  that is, $D h = h'$ as distributions.
  On the other hand, a simple computation shows that $g = h'$. Hence $g = D h$ as a distribution.

  $h$ is a bounded function, and so it is a tempered distribution. A derivative of a tempered distribution is itself a tempered distribution, and so $g$ is a tempered distribution, as required.

=
The Hahn–Banach theorem states that if $X$ is a locally convex topological vector space, $M subset.eq X$ is a subspace of $X$, and $f$ is a continuous linear functional on $M$ with respect to the subspace topology it inherits from $X$, then there is $Lambda in X^*$ which extends $f$.

@ex-3 does not contradict the theorem, since $f$ from there induces a continuous linear functional on the space $cal(D)(Omega)$ with respect to its standard topology, which is different from the topology it inherits from $Sn$.
So the hypotheses of the theorem do not hold in the first place, and there is no problem with the conclusion failing.

=
+ Let $psi in cal(D)(RR^n)$ such that $psi >= 0$ on all of $RR^n$, $psi = 0$ outside $overline(B(0, 1))$ and $psi > 1$ on $B(0, 1)$. // TODO: ψ > 1 on B(0,1) contradicts continuity with ψ = 0 outside the closed ball; probably ψ > 0?
  Put $psi_m = e^(-m) psi(x - m e_1)$. Then for every $m$, the support of $psi_m$ is $overline(B(m e_1, 1))$, and so there is no compact set which contains the support of $psi_m$ for every $m$.
  Hence ${psi_m}$ does not converge in $cal(D)(RR^n)$.

  Let $alpha$ be a multi-index and $P$ a polynomial. Then for every $m$
  $
    norm(P dot D^alpha psi_m)_oo &= e^(-m) max_(x in B(m e_1, 1)) |P(x) D^alpha psi(x - m e_1)| \
    &<= e^(-m) norm(D^alpha psi)_oo max_(x in B(m e_1, 1)) |P(x)| stretch(->)_(m -> oo) 0
  $
  and so $P dot D^alpha psi_m stretch(->)_(m -> oo) 0$ uniformly on $RR^n$.
  Since $alpha, P$ are arbitrary we get $psi_m stretch(->)_(m -> oo) 0$ in $Sn$, as required.

+ For every $m$ define $P_m (x) = sum_(j=1)^m (j!)^(-1) x^j$. Then $P_m stretch(->)_(m -> oo) exp$ uniformly on compact subsets of $RR$. // TODO: sum should start at j = 0 to converge to exp
  Then for every $phi in cal(D)(RR)$, if $K$ is the support of $phi$, we get
  $
    integral_RR P_m phi dif m_n = integral_K P_m phi dif m_n stretch(->)_(m -> oo) integral_K e^x phi(x) dif m_n (x) = integral_RR e^x phi(x) dif m_n (x)
  $
  and so $P_m -> exp$ in $cal(D)'(RR)$, as required.

  On the other hand, if by contradiction there is $u in cal(S)'_1$ such that $P_m -> u$ in $cal(S)'_1$, then in particular for every $phi in cal(D)(RR)$ we have $integral_RR P_m phi dif m_n -> u(phi)$, but then by what we saw we get
  $ u(phi) = integral_RR e^x phi(x) dif m_n (x) $
  for every $phi in cal(D)(RR)$, and we already saw in @ex-3 that the distribution $phi |-> integral_RR e^x phi(x) dif m_n (x)$ cannot be extended to $cal(S)_1$, so we got a contradiction.
  Hence $P_m$ does not converge in $cal(S)'_1$, as required.
