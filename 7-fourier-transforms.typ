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
Let $N$ be large enough that $integral_(RR^n) (1 + |y|^2)^(-2N) dif m_n (y) < oo$.
Since $f, g in Sn$, the functions $y |-> y^gamma D^alpha g(y)$ and $y |-> y^(beta - gamma) f(y)$ are in $Sn$ for every $gamma <= beta$.
Then there is $M$ for which $abs((1 + |y|^2)^N y^(beta - gamma) f(y)), abs((1 + |y|^2)^N y^gamma (D^alpha g)(y)) < M$ for every $y$.
That is, for every $y$ we have $abs(y^gamma (D^alpha g)(y))^2 < M^2 (1 + |y|^2)^(-2N)$ and also $abs(y^(beta - gamma) f(y))^2 < M^2 (1 + |y|^2)^(-2N)$.
Then for every $x in RR^n$ we get
$
  abs(x^beta (D^alpha (f * g))(x)) &<= sum_(gamma <= beta) |c_(beta gamma)| (integral_(RR^n) M^2 (1 + |y|^2)^(-2N) dif m_n (y))^(1\/2) \
  &quad dot (integral_(RR^n) M^2 (1 + |y|^2)^(-2N) dif m_n (y))^(1\/2) \
  &= sum_(gamma <= beta) |c_(beta gamma)| M^2 integral_(RR^n) (1 + |y|^2)^(-2N) dif m_n (y) < oo
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
  Now let $epsilon > 0$. By what we saw, there is $delta > 0$ such that if $|x| < delta$ then $integral_(RR^n) |e^(i x dot t) - 1| dif mu(t) < epsilon$.
  Then for every $a, b in RR^n$, if $|a - b| < delta$ we get
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
