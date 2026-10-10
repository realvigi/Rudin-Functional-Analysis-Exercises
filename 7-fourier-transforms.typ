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
Put $Q(x) = 1 + abs(x)^2$, and for every $N$ put $p_N (f) = max_(|alpha| <= N) norm(Q^N D_alpha f)_oo$ and $V_N = {f in Sn : p_N (f) < N^(-1)}$.
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

=
Let $alpha$ be a multi-index, $P$ a polynomial and $g in Sn$.
It is clear that the maps $u |-> D^alpha u$, $u |-> P u$, $u |-> g u$ are all linear maps from $cal(S)'_n$ to itself.
So in order to show that they are continuous, it suffices to show continuity at $0$.

Let $V$ be a neighborhood of $0$ in $cal(S)'_n$. Then there are $f_1, ..., f_m in Sn$ and $epsilon > 0$ for which
$ inter.big_(j=1)^m {u in cal(S)'_n : |u(f_j)| < epsilon} subset.eq V $
Put
$
  U_1 &= inter.big_(j=1)^m {u in cal(S)'_n : |u(D^alpha f_j)| < epsilon} \
  U_2 &= inter.big_(j=1)^m {u in cal(S)'_n : |u(P f_j)| < epsilon} \
  U_3 &= inter.big_(j=1)^m {u in cal(S)'_n : |u(g f_j)| < epsilon}
$
Then $U_1, U_2, U_3$ are neighborhoods of $0$ in $cal(S)'_n$, and
$
  {D^alpha u : u in U_1} &subset.eq inter.big_(j=1)^m {D^alpha u : u in cal(S)'_n, |u(D^alpha f_j)| < epsilon} \
  &= inter.big_(j=1)^m {D^alpha u : u in cal(S)'_n, |D^alpha u(f_j)| < epsilon} subset.eq V \
  {P u : u in U_2} &= inter.big_(j=1)^m {P u : u in cal(S)'_n, |u(P f_j)| < epsilon} \
  &= inter.big_(j=1)^m {P u : u in cal(S)'_n, |(P u)(f_j)| < epsilon} \
  &subset.eq inter.big_(j=1)^m {u in cal(S)'_n : |u(f_j)| < epsilon} subset.eq V \
  {g u : u in U_3} &= inter.big_(j=1)^m {g u : u in cal(S)'_n, |u(g f_j)| < epsilon} \
  &= inter.big_(j=1)^m {g u : u in cal(S)'_n, |(g u)(f_j)| < epsilon} \
  &subset.eq inter.big_(j=1)^m {u in cal(S)'_n : |u(f_j)| < epsilon} subset.eq V
$
which shows that the three maps above are indeed weak\*-continuous, as required.

=
Denote by $Phi$ the Fourier transform on $Sn$, and by $rho$ the reflection operator.
Fix $x in RR^n$. Then for every $phi in Sn$
$
  hat(tau_x u)(phi) &= (tau_x u)(Phi phi) = u(tau_(-x) Phi phi) = u(Phi^4 (tau_(-x) Phi phi)) = u(Phi^3 (e_x Phi^2 phi)) \
  &= u(Phi rho (e_x rho phi)) = u(Phi (e_(-x) phi)) = hat(u)(e_(-x) phi) = (e_(-x) u)(phi)
$
and so $hat(tau_x u) = e_(-x) u$, as required.

Also, for every $phi in Sn$
$
  hat(e_x u)(phi) = (e_x u)(hat(phi)) = u(e_x hat(phi)) = u(hat(tau_(-x) phi)) = hat(u)(tau_(-x) phi) = (tau_x hat(u))(phi)
$
and so $hat(e_x u) = tau_x hat(u)$, as required.

=
Denote by $Phi$ the Fourier transform on $cal(S)'_n$.
Since $f in L^1 (RR^n)$, $hat(f) = lambda f$, and $hat(f) = Phi f$ in the distributional sense, we get $Phi^k f in L^1 (RR^n)$ for every $k$, and also $Phi^k f = lambda^k f$ for every $k$.
But $Phi^4$ is the identity, and so we get $f = lambda^4 f$, where the equality is in $cal(S)'_n$.
Then for every $phi in cal(D)(RR^n)$
$ integral_(RR^n) f phi dif m_n = lambda^4 integral_(RR^n) f phi dif m_n $
Since $f != 0$, in particular there is $phi$ for which $integral_(RR^n) f phi dif m_n != 0$, and so we get $lambda^4 = 1$, that is, $lambda$ is a root of unity of order $4$.

=
Let $f, g in Sn$.

#claim[$f * g in C^oo (RR^n)$, and $D^alpha (f * g) = f * D^alpha g$ for every multi-index $alpha$.] <conv-smooth>
#proof[
  There is a sequence ${phi_k}$ in $cal(D)(RR^n)$ for which $phi_k -> g$ in $Sn$.
  In particular, for every $alpha$ we have $D^alpha phi_k -> D^alpha g$ uniformly on all of $RR^n$, and in particular ${D^alpha phi_k}$ is a uniformly Cauchy sequence on $RR^n$.
  For every $k$ we have $f * phi_k in C^oo (RR^n)$, and for every $alpha$ we have $D^alpha (f * phi_k) = f * D^alpha phi_k$.
  Then for every $k, j$ and every $alpha$ we get
  $
    norm(D^alpha (f * phi_k) - D^alpha (f * phi_j))_oo &<= sup_(x in RR^n) integral_(RR^n) |f(x - y)| |D^alpha phi_k (y) - D^alpha phi_j (y)| dif m_n (y) \
    &<= norm(f)_1 norm(D^alpha phi_k - D^alpha phi_j)_oo
  $
  Since $f in Sn$ we have $norm(f)_1 < oo$, and so since ${D^alpha phi_k}$ is uniformly Cauchy on all of $RR^n$, we get that ${D^alpha (f * phi_k)}$ is a uniformly Cauchy sequence on all of $RR^n$.
  Then ${f * phi_k}$ is a Cauchy sequence in $C^oo (RR^n)$.
  But $C^oo (RR^n)$ is a complete space, and so there is $h in C^oo (RR^n)$ for which $f * phi_k stretch(->)_(k -> oo) h$ in $C^oo (RR^n)$.
  Then in particular, for every $x$ and every $alpha$ we have $(f * D^alpha phi_k)(x) = D^alpha (f * phi_k)(x) stretch(->)_(k -> oo) D^alpha h(x)$.

  On the other hand, for every $alpha$ we have $D^alpha phi_k -> D^alpha g$ uniformly on all of $RR^n$, and so for every $x$
  $
    |(f * D^alpha phi_k)(x) - (f * D^alpha g)(x)| &<= integral_(RR^n) |f(x - y)| |D^alpha phi_k (y) - D^alpha g(y)| dif m_n (y) \
    &<= norm(f)_1 norm(D^alpha phi_k - D^alpha g)_oo stretch(->)_(k -> oo) 0
  $
  and so $(f * D^alpha phi_k)(x) -> (f * D^alpha g)(x)$ for every $x$.
  Hence for every $alpha$ we have $f * D^alpha g = D^alpha h$.
  In particular, for $alpha = 0$ we get $f * g = h in C^oo (RR^n)$, and for every $alpha$ we get $D^alpha (f * g) = f * D^alpha g$.
]

Fix two multi-indices $alpha, beta$. Then for every $x, y in RR^n$
$
  D^beta (e_x e_y) &= sum_(gamma <= beta) c_(beta gamma) (D^(beta - gamma) e_x) (D^gamma e_y) \
  &= sum_(gamma <= beta) c_(beta gamma) (i^(|beta| - |gamma|) x^(beta - gamma) e_x) (i^(|gamma|) y^gamma e_y) \
  &= i^(|beta|) sum_(gamma <= beta) c_(beta gamma) x^(beta - gamma) y^gamma e_(x + y)
$
and on the other hand
$ D^beta (e_x e_y) = D^beta e_(x + y) = i^(|beta|) (x + y)^beta e_(x + y) $
that is, for every $x, y in RR^n$ we got the equality
$ (x + y)^beta e_(x + y) = sum_(gamma <= beta) c_(beta gamma) x^(beta - gamma) y^gamma e_(x + y) $
and if we evaluate both sides at $0$ we get the equality $(x + y)^beta = sum_(gamma <= beta) c_(beta gamma) x^(beta - gamma) y^gamma$ for every $x, y in RR^n$.

Then, using @conv-smooth, for every $x in RR^n$ we get
$
  abs(x^beta (D^alpha (f * g))(x)) &= abs(x^beta (f * D^alpha g)(x)) \
  &= abs(x^beta integral_(RR^n) f(x - y) (D^alpha g)(y) dif m_n (y)) \
  &= abs(integral_(RR^n) (x - y + y)^beta f(x - y) (D^alpha g)(y) dif m_n (y)) \
  &= abs(sum_(gamma <= beta) c_(beta gamma) integral_(RR^n) (x - y)^(beta - gamma) f(x - y) y^gamma (D^alpha g)(y) dif m_n (y)) \
  &<= sum_(gamma <= beta) |c_(beta gamma)| integral_(RR^n) abs((x - y)^(beta - gamma) f(x - y)) abs(y^gamma (D^alpha g)(y)) dif m_n (y) \
  &<= sum_(gamma <= beta) |c_(beta gamma)| (integral_(RR^n) abs((x - y)^(beta - gamma) f(x - y))^2 dif m_n (y))^(1\/2) \
  &quad dot (integral_(RR^n) abs(y^gamma (D^alpha g)(y))^2 dif m_n (y))^(1\/2) \
  &= sum_(gamma <= beta) |c_(beta gamma)| (integral_(RR^n) abs(y^(beta - gamma) f(y))^2 dif m_n (y))^(1\/2) \
  &quad dot (integral_(RR^n) abs(y^gamma (D^alpha g)(y))^2 dif m_n (y))^(1\/2)
$
Let $N$ be large enough that $integral_(RR^n) (1 + abs(y)^2)^(-2N) dif m_n (y) < oo$.
Since $f, g in Sn$, the functions $y |-> y^gamma D^alpha g(y)$ and $y |-> y^(beta - gamma) f(y)$ are in $Sn$ for every $gamma <= beta$.
Then there is $M$ for which $abs((1 + abs(y)^2)^N y^(beta - gamma) f(y)), abs((1 + abs(y)^2)^N y^gamma (D^alpha g)(y)) < M$ for every $y$.
That is, for every $y$ we have $abs(y^gamma (D^alpha g)(y))^2 < M^2 (1 + abs(y)^2)^(-2N)$ and also $abs(y^(beta - gamma) f(y))^2 < M^2 (1 + abs(y)^2)^(-2N)$.
Then for every $x in RR^n$ we get
$
  abs(x^beta (D^alpha (f * g))(x)) &<= sum_(gamma <= beta) |c_(beta gamma)| (integral_(RR^n) M^2 (1 + abs(y)^2)^(-2N) dif m_n (y))^(1\/2) \
  &quad dot (integral_(RR^n) M^2 (1 + abs(y)^2)^(-2N) dif m_n (y))^(1\/2) \
  &= sum_(gamma <= beta) |c_(beta gamma)| M^2 integral_(RR^n) (1 + abs(y)^2)^(-2N) dif m_n (y) < oo
$
This shows that for all multi-indices $alpha, beta$, the function $x |-> x^beta D^alpha (f * g)(x)$ is bounded.
Now if $P(x) = sum_beta d_beta x^beta$ is any polynomial, then for every $beta$ there is $M_beta > 0$ for which
$ sup_(x in RR^n) abs(x^beta D^alpha (f * g)(x)) <= M_beta $
and so
$
  sup_(x in RR^n) |P(x) D^alpha (f * g)(x)| &= sup_(x in RR^n) abs(sum_beta d_beta x^beta D^alpha (f * g)(x)) \
  &<= sum_beta |d_beta| sup_(x in RR^n) abs(x^beta D^alpha (f * g)(x)) \
  &<= sum_beta |d_beta| M_beta < oo
$
that is, $P dot D^alpha (f * g)$ is bounded for every $alpha$ and every $P$, and so $f * g in Sn$, as required.

=
+ We need to show that for every $phi in cal(D)(Omega)$ we have $integral_(RR^n) hat(phi) dif mu = integral_(RR^n) hat(mu) phi dif m_n$, where $hat(mu)$ is defined as a function as in the exercise.
  We have
  $ integral_(RR^n) integral_(RR^n) |phi(x) e^(-i t dot x)| dif m_n (x) dif mu(t) = norm(phi)_1 mu(RR^n) < oo $
  and so by Fubini's theorem
  $
    integral_(RR^n) integral_(RR^n) phi(x) e^(-i t dot x) dif m_n (x) dif mu(t) = integral_(RR^n) integral_(RR^n) phi(x) e^(-i t dot x) dif mu(t) dif m_n (x)
  $
  and so we get
  $
    integral_(RR^n) hat(phi) dif mu &= integral_(RR^n) integral_(RR^n) phi(x) e^(-i t dot x) dif m_n (x) dif mu(t) \
    &= integral_(RR^n) (integral_(RR^n) e^(-i t dot x) dif mu(t)) phi(x) dif m_n (x) \
    &= integral_(RR^n) hat(mu)(x) phi(x) dif m_n (x)
  $
  as required.

+ We show that $hat(mu)$ is bounded. Indeed, for every $x$
  $ |hat(mu)(x)| <= integral_(RR^n) |e^(-i x dot t)| dif mu(t) = integral_(RR^n) dif mu(t) = mu(RR^n) < oo $
  as required.

+ We show that $hat(mu)$ is uniformly continuous.
  We have $e^(i x dot t) - 1 stretch(->)_(x -> 0) 0$, and also $|e^(i x dot t) - 1| <= 2$ for every $x, t in RR^n$, and $2 in L^1 (mu)$ since $mu(RR^n) < oo$.
  Then by the dominated convergence theorem we get
  $ integral_(RR^n) |e^(i x dot t) - 1| dif mu(t) stretch(->)_(x -> 0) 0 $
  Now let $epsilon > 0$. By what we saw, there is $delta > 0$ such that if $abs(x) < delta$ then $integral_(RR^n) |e^(i x dot t) - 1| dif mu(t) < epsilon$.
  Then for every $a, b in RR^n$, if $abs(a - b) < delta$ we get
  $
    |hat(mu)(a) - hat(mu)(b)| <= integral_(RR^n) |e^(-i a dot t) - e^(-i b dot t)| dif mu(t) = integral_(RR^n) |e^(i (b - a) dot t) - 1| dif mu(t) < epsilon
  $
  and this shows that $hat(mu)$ is uniformly continuous, as required.

=
For every $phi in Sn$ define $u(phi) = (Lambda rho phi)(0)$.
$rho$ is a continuous linear operator on $Sn$, and evaluation at $0$ is a continuous linear functional on $C(RR^n)$, and so $u$ is a continuous linear functional on $Sn$, that is, $u in cal(S)'_n$.
For every $phi in Sn$ and every $x in RR^n$
$
  (u * phi)(x) = u(tau_x rho phi) = (Lambda rho tau_x rho phi)(0) = (Lambda tau_(-x) rho rho phi)(0) = (tau_(-x) Lambda phi)(0) = (Lambda phi)(x)
$
and so $Lambda phi = u * phi$ for every $phi in Sn$, as required.

=
#claim[For every $phi in Sn$ there is $C_phi > 0$ such that $norm(tau_y phi - phi)_oo <= C_phi abs(y)$ for every $y in RR^n$.] <lipschitz>
#proof[
  Let $phi in Sn$. Put $C = (sum_(i=1)^n norm(D^(e_i) phi)_oo^2)^(1\/2)$.
  Fix $x, y in RR^n$. Put $g(t) = phi(x + t(y - x))$.
  Then $g$ is continuously differentiable, and for every $t$
  $
    |g'(t)| &= |(y - x) dot nabla phi(t)| <= abs(y - x) |nabla phi(t)| = abs(y - x) (sum_(i=1)^n (D^(e_i) phi(t))^2)^(1\/2) \
    &<= abs(y - x) (sum_(i=1)^n norm(D^(e_i) phi)_oo^2)^(1\/2) = C abs(y - x)
  $
  and so by the mean value theorem, there is $c in [0, 1]$ for which
  $ |phi(y) - phi(x)| = |g(1) - g(0)| = |g'(c)| <= C abs(y - x) $
  Since $x, y$ are arbitrary, we got that $|phi(y) - phi(x)| <= C abs(y - x)$ for every $x, y in RR^n$.
]

#claim[If ${h_j}$ is an approximate identity, then $h_j * phi -> phi$ in the topology of $Sn$ for every $phi in Sn$.] <approx-identity>
#proof[
  Let $phi in Sn$, and let $alpha, beta$ be multi-indices. For every $gamma$ put $Q_gamma (x) = x^gamma$.
  For every $gamma <= beta$ and every $j$ put
  $ f_(j, gamma) (x) = integral_(RR^n) y^(beta - gamma) h_j (y) (x - y)^gamma D^alpha phi(x - y) dif m_n (y) $
  Then for every $j$ and every $x$
  $
    x^beta D^alpha (h_j * phi)(x) - x^beta D^alpha phi(x) &= integral_(RR^n) (y + x - y)^beta h_j (y) D^alpha phi(x - y) dif m_n (y) - x^beta D^alpha phi(x) \
    &= sum_(gamma <= beta) c_(beta gamma) integral_(RR^n) y^(beta - gamma) h_j (y) (x - y)^gamma D^alpha phi(x - y) dif m_n (y) - x^beta D^alpha phi(x) \
    &= (sum_(gamma <= beta) c_(beta gamma) f_(j, gamma) (x)) - x^beta D^alpha phi(x)
  $
  and since $c_(beta beta) = 1$, for every $j$ we got the equality
  $
    Q_beta D^alpha (h_j * phi) - Q_beta D^alpha phi = (f_(j, beta) - x^beta D^alpha phi) + (sum_(gamma < beta) c_(beta gamma) f_(j, gamma))
  $
  Since $Q_beta D^alpha phi in Sn$, by @lipschitz we get
  $
    norm(f_(j, beta) - x^beta D^alpha phi)_oo &= sup_(x in RR^n) abs(integral_(RR^n) h_j (y) ((x - y)^beta D^alpha phi(x - y) - x^beta D^alpha phi(x)) dif m_n (y)) \
    &<= sup_(x in RR^n) integral_(RR^n) h_j (y) |(tau_y (Q_beta D^alpha phi))(x) - (Q_beta D^alpha phi)(x)| dif m_n (y) \
    &<= sup_(x in RR^n) integral_(B(0, j^(-1))) h_j (y) norm(tau_y (Q_beta D^alpha phi) - Q_beta D^alpha phi)_oo dif m_n (y) \
    &<= sup_(x in RR^n) integral_(B(0, j^(-1))) h_j (y) C_(Q_beta D^alpha phi) abs(y) dif m_n (y) \
    &<= C_(Q_beta D^alpha phi) j^(-1) sup_(x in RR^n) integral_(B(0, j^(-1))) h_j (y) dif m_n (y) = C_(Q_beta D^alpha phi) j^(-1) stretch(->)_(j -> oo) 0
  $
  and so $f_(j, beta) - x^beta D^alpha phi -> 0$ uniformly on $RR^n$.

  Also, for every $gamma < beta$ we have $|beta - gamma| >= 1$, and so
  $
    norm(f_(j, gamma))_oo &<= sup_(x in RR^n) integral_(RR^n) |y^(beta - gamma)| h_j (y) |(x - y)^gamma D^alpha phi(x - y)| dif m_n (y) \
    &<= norm(Q_gamma D^alpha phi)_oo integral_(B(0, j^(-1))) |y^(beta - gamma)| h_j (y) dif m_n (y) \
    &<= norm(Q_gamma D^alpha phi)_oo integral_(B(0, j^(-1))) abs(y)^(|beta - gamma|) h_j (y) dif m_n (y) \
    &<= norm(Q_gamma D^alpha phi)_oo j^(-|beta - gamma|) integral_(B(0, j^(-1))) h_j (y) dif m_n (y) \
    &= norm(Q_gamma D^alpha phi)_oo j^(-|beta - gamma|) stretch(->)_(j -> oo) 0
  $
  and so $f_(j, gamma) -> 0$ uniformly on all of $RR^n$.

  This shows that $Q_beta D^alpha (h_j * phi) - Q_beta D^alpha phi -> 0$ uniformly on $RR^n$, that is, $Q_beta D^alpha (h_j * phi) -> Q_beta D^alpha phi$ uniformly on $RR^n$, for all multi-indices $alpha, beta$ and every $phi in Sn$.
  This shows that for every $phi in Sn$, every multi-index $alpha$ and every polynomial $P$ we have $P D^alpha (h_j * phi) -> P D^alpha phi$ uniformly on $RR^n$.
]

But if ${h_j}$ is an approximate identity, then ${rho h_j}$ is also an approximate identity, and so by @approx-identity, for every $u in cal(S)'_n$ and every $phi in Sn$ we get
$
  (u * h_j)(phi) &= ((u * h_j) * rho phi)(0) = (u * (h_j * rho phi))(0) = u(rho (h_j * rho phi)) \
  &= u((rho h_j) * phi) stretch(->)_(j -> oo) u(phi)
$
that is, $u * h_j -> u$ in the weak\* topology of $cal(S)'_n$, as required.

=
// TODO: in the first part, sequences and points are taken in X, but f is only defined on A; probably A was meant
+ Let ${x_n}$ be a Cauchy sequence in $X$.
  Let $epsilon > 0$. Then there is $delta > 0$ such that for every $a, b in X$, if $d(a, b) < delta$ then $d(f(a), f(b)) < epsilon$.
  Since ${x_n}$ is a Cauchy sequence, there is $N$ such that $d(x_m, x_n) < delta$ for every $m, n >= N$.
  Then $d(f(x_m), f(x_n)) < epsilon$ for every $m, n >= N$.
  This shows that ${f(x_n)}$ is a Cauchy sequence in $Y$.
  That is, we showed that the image of every Cauchy sequence in $X$ is a Cauchy sequence in $Y$. Since $Y$ is complete, we get that the image of a convergent sequence in $X$ is a convergent sequence in $Y$.

  Now suppose ${a_n}, {b_n}$ are two sequences in $X$ which both converge to $x_0 in X$.
  By what we saw, there are $y_1, y_2 in Y$ for which $f(a_n) -> y_1$ and $f(b_n) -> y_2$ in $Y$.
  Let $epsilon > 0$. Then there is $N$ such that $d(y_1, f(a_n)), d(f(b_n), y_2) < epsilon$ for every $n > N$.
  Also, there is $delta > 0$ such that for every $a, b in X$, if $d(a, b) < delta$ then $d(f(a), f(b)) < epsilon$.
  Since $a_n -> x_0$ and also $b_n -> x_0$, we have $d(a_n, b_n) -> 0$.
  Then there is some $m > N$ for which $d(a_m, b_m) < delta$. Then we get
  $
    d(y_1, y_2) &<= d(y_1, f(a_m)) + d(f(a_m), f(b_m)) + d(f(b_m), y_2) \
    &< epsilon + epsilon + epsilon = 3 epsilon
  $
  and since $epsilon$ is arbitrary we get $d(y_1, y_2) = 0$, that is, $y_1 = y_2$.
  This shows that if two sequences converge to the same limit in $X$, then their images in $Y$ also converge to the same limit.

  Now for $x in X$, take a sequence ${a_n}$ in $A$ for which $a_n -> x$, and define $F(x) = lim_(n -> oo) f(a_n)$.
  By what we saw, the limit always exists, and it does not depend on the specific sequence we chose, but only on its limit, that is, only on $x$.
  So $F(x)$ is well defined.
  If $a in A$, then the constant sequence $a_n = a$ satisfies $a_n -> a$, and so we get $F(a) = lim_(n -> oo) f(a_n) = f(a)$. That is, $F$ extends $f$, as required.

  Let $x_0 in X$ and $epsilon > 0$. Let $delta > 0$ such that if $d(a, b) < 3 delta$ then $d(f(a), f(b)) < epsilon$, for every $a, b in A$.
  There is a sequence ${a_n}$ in $A$ for which $a_n -> x_0$ and $f(a_n) -> F(x_0)$.
  In particular, there is $a_0 in A$ for which $d(F(x_0), f(a_0)) < epsilon$ and also $d(x_0, a_0) < delta$.
  Let $x in X$ such that $d(x_0, x) < delta$.
  Then again by the same argument, there is $a in A$ for which $d(x, a) < delta$ and $d(F(x), f(a)) < epsilon$.
  Then
  $ d(a_0, a) <= d(a_0, x_0) + d(x_0, x) + d(x, a) < 3 delta $
  and so $d(f(a_0), f(a)) < epsilon$. Then
  $
    d(F(x_0), F(x)) &<= d(F(x_0), f(a_0)) + d(f(a_0), f(a)) + d(f(a), F(x)) \
    &< 3 epsilon
  $
  That is, $F(x) in B_(3 epsilon) (F(x_0))$ for every $x in B_delta (x_0)$.
  This completes the proof that $F$ is continuous.

  Finally, we need to show that $F$ is the unique continuous extension of $f$ to all of $X$.
  Let $G : X -> Y$ be continuous, with $G(a) = f(a)$ for every $a in A$. Let $x in X$. Then there is a sequence ${a_n}$ in $A$ for which $a_n -> x$.
  By the continuity of $G$ we get $f(a_n) = G(a_n) -> G(x)$, but on the other hand $f(a_n) -> F(x)$ directly from the definition.
  Then by the uniqueness of the limit in a metric space we get $F(x) = G(x)$.
  So indeed $F = G$, as required.

+ Suppose $f : A -> Y$ is an isometry, and $F$ is the unique continuous extension of $f$ to $X$.

  #claim[$d(F(x_1), F(x_2)) <= d(x_1, x_2)$ for every $x_1, x_2 in X$.] <extension-contraction>
  #proof[
    Let $x_1, x_2 in X$. Let $epsilon > 0$. By the continuity of $F$, there is $delta > 0$ for which $F(B_delta (x_i)) subset.eq B_epsilon (F(x_i))$ for $i = 1, 2$.
    By the density of $A$, for $i = 1, 2$ there is $a_i in B_delta (x_i) inter B_epsilon (x_i)$.
    Then $f(a_i) = F(a_i) in B_epsilon (F(x_i))$ for $i = 1, 2$. Also
    $
      d(a_1, a_2) &<= d(a_1, x_1) + d(x_1, x_2) + d(x_2, a_2) \
      &< d(x_1, x_2) + 2 epsilon
    $
    Then we get
    $
      d(F(x_1), F(x_2)) &<= d(F(x_1), f(a_1)) + d(f(a_1), f(a_2)) + d(f(a_2), F(x_2)) \
      &<= d(F(x_1), f(a_1)) + d(a_1, a_2) + d(f(a_2), F(x_2)) \
      &< epsilon + d(x_1, x_2) + 2 epsilon + epsilon = d(x_1, x_2) + 4 epsilon
    $
    Since $epsilon$ is arbitrary, we get $d(F(x_1), F(x_2)) <= d(x_1, x_2)$.
  ]

  By the continuity of $F$ and the density of $A$ in $X$, $f(A)$ is dense in $F(X)$.
  Also, $f^(-1)$ is an isometry from $f(A)$ to $X$.
  Then there exists a unique continuous function $G : F(X) -> X$ for which $G(y) = f^(-1) (y)$ for every $y in f(A)$.
  Let $x in X$ be arbitrary, and take a sequence ${a_n}$ in $A$ for which $a_n -> x$.
  Then $F(a_n) -> F(x)$, and so
  $ G(F(a_n)) -> G(F(x)) $
  but on the other hand, for every $n$
  $ G(F(a_n)) = G(f(a_n)) = f^(-1) (f(a_n)) = a_n $
  and so $a_n -> G(F(x))$, and by the uniqueness of the limit we got $G(F(x)) = x$.
  That is, $G compose F$ is the identity function.

  Exactly the same argument as in the proof of @extension-contraction, applied to $f^(-1)$ and $G$, shows that $d(G(y_1), G(y_2)) <= d(y_1, y_2)$ for every $y_1, y_2 in F(X)$.
  That is, for every $x_1, x_2 in X$
  $ d(x_1, x_2) = d(G(F(x_1)), G(F(x_2))) <= d(F(x_1), F(x_2)) $
  and so, together with @extension-contraction, for every $x_1, x_2 in X$
  $ d(x_1, x_2) = d(F(x_1), F(x_2)) $
  that is, $F$ is an isometry, as required.

  Since $F : X -> F(X)$ is an isometry and $X$ is complete, $F(X)$ is also a complete metric space.
  Then if ${y_n}$ is a sequence in $F(X)$ which converges to some $y in Y$, then in particular ${y_n}$ is a Cauchy sequence, and so it must converge in $F(X)$, that is, there is $y' in F(X)$ for which $y_n -> y'$ in $F(X)$, and so $y_n -> y'$ in $Y$, and so by the uniqueness of the limit $y = y' in F(X)$.
  This shows that $F(X)$ is closed, as required.

=
Let $B$ be the closed unit ball in $RR^n$.
By the Paley–Wiener theorem for distributions with compact support, we get that for every $epsilon > 0$ there is $u_epsilon in cal(D)'(RR^n)$ with compact support, whose support is contained in $epsilon B$, and such that $F(z) = u_epsilon (e_(-z))$ for every $z$.
Then by the other direction of the same theorem, for every $epsilon > 0$ the restriction of $F$ to $RR^n$ is the Fourier transform of $u_epsilon$.
Then in particular $hat(u_epsilon) = hat(u_(epsilon'))$ for every $epsilon, epsilon' > 0$, and since the Fourier transform is injective, $u_epsilon = u_(epsilon')$ for every $epsilon, epsilon' > 0$.
Then there is $u in cal(D)'(RR^n)$ for which $u = u_epsilon$ for every $epsilon > 0$.
Then the support of $u$ is contained in $epsilon B$ for every $epsilon > 0$, and so the support of $u$ is contained in ${0}$.
Then there are a multi-index $alpha$ and scalars $c_beta$ for every $beta <= alpha$ such that $u = sum_(beta <= alpha) c_beta D^beta delta$.
Also, we get $F(z) = u_1 (e_(-z)) = u(e_(-z))$ for every $z in CC^n$.
Then for every $z in CC^n$
$
  F(z) &= sum_(beta <= alpha) c_beta D^beta delta(e_(-z)) = sum_(beta <= alpha) c_beta (-1)^(|beta|) delta(D^beta e_(-z)) \
  &= sum_(beta <= alpha) c_beta (-1)^(|beta|) delta((-i)^(|beta|) z^beta e_(-z)) \
  &= sum_(beta <= alpha) c_beta (-1)^(|beta|) (-i)^(|beta|) z^beta delta(e_(-z)) \
  &= sum_(beta <= alpha) c_beta i^(|beta|) z^beta e_(-z) (0) = sum_(beta <= alpha) c_beta i^(|beta|) z^beta
$
that is, $F$ is indeed a polynomial, as required.

=
Fix $z = x + i y$.
For every $s > 0$ and $lambda in CC$ define $g_s (lambda) = (1 - i s lambda)^(-N-1) e^(i r abs(y) lambda) f(x + lambda y)$. Then $g_s$ is entire in $CC$.
Fix $s$.
For every $A > 0$, let $Omega_A$ be the intersection of the open disc of radius $A$ in $CC$ with the upper half-plane.
Then the boundary of $Omega_A$ is $[-A, A] union {A e^(i t) : 0 <= t <= pi}$.
For $lambda in [-A, A]$ we have
$
  |g_s (lambda)| &= |1 - i s lambda|^(-N-1) |e^(i r abs(y) lambda)| |f(x + lambda y)| \
  &<= |1 - i s lambda|^(-N-1) = 1 / (1 + s^2 lambda^2)^((N+1)\/2) <= 1
$
and also, for every $t in [0, pi]$ we have $sin t >= 0$, and so
$
  |exp(i r abs(y) A e^(i t))| |f(x + A e^(i t) y)| &<= e^(-r A abs(y) sin t) (1 + |x + A e^(i t) y|)^N e^(r A abs(y) abs(sin t)) \
  &= (1 + |x + A e^(i t) y|)^N
$
and so for every $A$ for which $s A > 1$, and every $t in [0, pi]$
$
  |g_s (A e^(i t))| &= |1 - i s A e^(i t)|^(-N-1) |exp(i r abs(y) A e^(i t))| |f(x + A e^(i t) y)| \
  &<= (1 + |x + A e^(i t) y|)^N / (|1 - i s A e^(i t)|^(N+1)) <= (1 + abs(x) + abs(y) A)^N / (s A - 1)^(N+1)
$
But
$ (1 + abs(x) + abs(y) A)^N / (s A - 1)^(N+1) stretch(->)_(A -> oo) 0 $
and so there is some $A_0 > max{s^(-1), 1}$ for which
$ (1 + abs(x) + abs(y) A_0)^N / (s A_0 - 1)^(N+1) < 1 $
and then we get $|g_s (A_0 e^(i t))| < 1$ for every $t in [0, pi]$.
Then $|g_s| <= 1$ on the boundary of the domain $Omega_(A_0)$.
$overline(Omega_(A_0))$ is compact, and so by the maximum principle $|g_s| <= 1$ in $Omega_(A_0)$.
Since $A_0 > 1$, in particular $i in Omega_(A_0)$, and so $|g_s (i)| <= 1$. That is,
$ |(1 + s)^(-N-1) e^(-r abs(y)) f(x + i y)| <= 1 $
that is,
$ |f(z)| <= (1 + s)^(N+1) e^(r abs(y)) $
and since $s$ is arbitrary, the last inequality holds for every $s > 0$. But
$ (1 + s)^(N+1) e^(r abs(y)) stretch(->)_(s -> 0) e^(r abs(y)) $
and so we get $|f(z)| <= e^(r abs(y))$.
Since $z$ is arbitrary, we get $|f(z)| <= e^(r |op("Im") z|)$ for every $z in CC^n$.
