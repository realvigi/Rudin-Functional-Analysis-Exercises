#import "template/pset.typ": *
#show: pset.with(title: "Chapter 7 — Fourier Transforms")

#let Sn = $cal(S)_n$
#let Rn = $RR^n$

=
#problem[
  Suppose $A$ is an invertible linear operator on #Rn, $f in L^1(Rn)$, and $g(x) = f(A x)$.
  Express $hat(g)$ in terms of $hat(f)$. This generalized (d) of Theorem 7.2.
]
#solution[
  Using a change of variables we get
  $
    hat(g)(t) & = integral_(RR^n) g e_(-t) dif m_n = integral_(RR^n) (f compose A) e_(-t) dif m_n \
              & = 1/abs(det A) integral_(RR^n) f dot (e_(-t) compose A^(-1)) dif m_n \
              & = 1/abs(det A) integral_(RR^n) f(x) e^(-i(t dot A^(-1) x)) dif m_n (x) \
              & = 1/abs(det A) integral_(RR^n) f(x) e^(-i((A^(-1))^* t) dot x) dif m_n (x) \
              & = 1/abs(det A) hat(f)((A^(-1))^* t)
  $
  and so we got $hat(g) = abs(det A)^(-1) hat(f) compose (A^(-1))^*$.
]

=
#problem[
  Is the topology of #Sn induced by some invariant metric which turns the Fourier transform into an isometry of #Sn onto #Sn?
]
#solution[
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
    For $0 <= j <= 3$, the function $p_N compose Phi^j$ is a continuous map from $Sn$ to $[0, oo)$. // FIX: original has (0, ∞)
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
    d(hat(f), hat(g)) & = max_N (c_N q_N (hat(f) - hat(g))) / (1 + q_N (hat(f) - hat(g)))
                        = max_N (c_N q_N (hat(f - g))) / (1 + q_N (hat(f - g))) \
                      & = max_N (c_N q_N (f - g)) / (1 + q_N (f - g)) = d(f, g)
  $
  and so we found a metric $d$ on $Sn$ which induces the standard topology, is translation invariant, and with respect to which the Fourier transform is an isometry, as required.
]

= <ex-3>
+ #problem[
    Suppose $f(x) = e^x$ on the real line. Show that $f$ is not a tempered distribution.
  ]
  #solution[
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
    and of course $e^(-m) |P(m + 1)| stretch(->)_(m -> oo) 0$. Then $P dot D^alpha (e^(-m) (tau_m psi)) stretch(->)_(m -> oo) 0$ uniformly on $RR$, and so $e^(-m) tau_m psi stretch(->)_(m -> oo) 0$ in $cal(S)_1$.

    On the other hand, putting $psi_m = e^(-m) tau_m psi$, for every $m$ we have
    $
      integral_(-oo)^oo e^x psi_m (x) dif x = integral_(-oo)^oo e^(x - m) psi(x - m) dif x = integral_(-oo)^oo e^x psi(x) dif x >= integral_(-1\/2)^(1\/2) e^x dif x > 0
    $
    and in particular it is impossible that $integral_(-oo)^oo f psi_m dif m_n -> 0$ as $m -> oo$, and so $f$ cannot be extended to a continuous functional on $Sn$, that is, $f$ is not a tempered distribution, as required.
  ]

+ #problem[
    Suppose $g(x) = e^x cos(e^x)$ on the real line. Show that $g$ is a tempered distribution.
  ]
  #solution[

    Put $h(x) = sin(e^x)$. Let $h'$ be the ordinary derivative of $h$, and $D h$ the distributional derivative of $h$.
    $h'$ is continuous, and so by integration by parts, for every $phi in cal(D)(RR)$ we have
    $ D h(phi) = - integral_RR h phi' dif m_n = integral_RR h' phi dif m_n $
    that is, $D h = h'$ as distributions.
    On the other hand, a simple computation shows that $g = h'$. Hence $g = D h$ as a distribution.

    $h$ is a bounded function, and so it is a tempered distribution. A derivative of a tempered distribution is itself a tempered distribution, and so $g$ is a tempered distribution, as required.
  ]

=
#problem[
  By Exercise 3 there exist distributions in #Rn which are not tempered.
  Such distributions are continuous linear functionals on $cal(D)(Rn)$, which have no continuous linear extension to #Sn. Explain why this does not contradict the Hahn-Banach theorem.
]
#solution[
  The Hahn–Banach theorem states that if $X$ is a locally convex topological vector space, $M subset.eq X$ is a subspace of $X$, and $f$ is a continuous linear functional on $M$ with respect to the subspace topology it inherits from $X$, then there is $Lambda in X^*$ which extends $f$.

  @ex-3 does not contradict the theorem, since $f$ from there induces a continuous linear functional on the space $cal(D)(Omega)$ with respect to its standard topology, which is different from the topology it inherits from $Sn$.
  So the hypotheses of the theorem do not hold in the first place, and there is no problem with the conclusion failing.
]

=
+ #problem[
    Contruct a sequence in $cal(D)(Rn)$ which converges to 0 in the topology of #Sn but not in that of $cal(D)(Rn)$
  ]
  #solution[
    Let $psi in cal(D)(RR^n)$ such that $psi >= 0$ on all of $RR^n$, $psi = 0$ outside $overline(B(0, 1))$ and $psi > 0$ on $B(0, 1)$.
    Put $psi_m = e^(-m) psi(x - m e_1)$. Then for every $m$, the support of $psi_m$ is $overline(B(m e_1, 1))$, and so there is no compact set which contains the support of $psi_m$ for every $m$.
    Hence ${psi_m}$ does not converge in $cal(D)(RR^n)$.

    Let $alpha$ be a multi-index and $P$ a polynomial. Then for every $m$
    $
      norm(P dot D^alpha psi_m)_oo & = e^(-m) max_(x in B(m e_1, 1)) |P(x) D^alpha psi(x - m e_1)| \
                                   & <= e^(-m) norm(D^alpha psi)_oo max_(x in B(m e_1, 1)) |P(x)| stretch(->)_(m -> oo) 0
    $
    and so $P dot D^alpha psi_m stretch(->)_(m -> oo) 0$ uniformly on $RR^n$.
    Since $alpha, P$ are arbitrary we get $psi_m stretch(->)_(m -> oo) 0$ in $Sn$, as required.
  ]

+ #problem[
    Contruct a sequence of polynomials which converges in the topology of $cal(D)'(RR)$ but not in that of $cal(S)'_1$
  ]
  #solution[
    For every $m$ define $P_m (x) = sum_(j=0)^m (j!)^(-1) x^j$. Then $P_m stretch(->)_(m -> oo) exp$ uniformly on compact subsets of $RR$.
    Then for every $phi in cal(D)(RR)$, if $K$ is the support of $phi$, we get
    $
      integral_RR P_m phi dif m_1 = integral_K P_m phi dif m_1 stretch(->)_(m -> oo) integral_K e^x phi(x) dif m_1 (x) = integral_RR e^x phi(x) dif m_1 (x)
    $
    and so $P_m -> exp$ in $cal(D)'(RR)$, as required.

    On the other hand, if there is $u in cal(S)'_1$ such that $P_m -> u$ in $cal(S)'_1$, then in particular for every $phi in cal(D)(RR)$ we have $integral_RR P_m phi dif m_1 -> u(phi)$, but then by what we saw we get
    $ u(phi) = integral_RR e^x phi(x) dif m_1 (x) $
    for every $phi in cal(D)(RR)$, and we already saw in @ex-3 that the distribution $phi |-> integral_RR e^x phi(x) dif m_1 (x)$ cannot be extended to $cal(S)_1$, so we got a contradiction.
    Hence $P_m$ does not converge in $cal(S)'_1$, as required.
  ]

=
#problem[
  Prove taht the operations listed in Theorem 7.13 are _continuous_ mapping of $Sn'$ into $Sn'$.
]
#solution[
  Let $alpha$ be a multi-index, $P$ a polynomial and $g in Sn$.
  It is clear that the maps $u |-> D^alpha u$, $u |-> P u$, $u |-> g u$ are all linear maps from $cal(S)'_n$ to itself.
  So in order to show that they are continuous, it suffices to show continuity at $0$.

  Let $V$ be a neighborhood of $0$ in $cal(S)'_n$. Then there are $f_1, ..., f_m in Sn$ and $epsilon > 0$ for which
  $ inter.big_(j=1)^m {u in cal(S)'_n : |u(f_j)| < epsilon} subset.eq V. $
  Put
  $
    U_1 & = inter.big_(j=1)^m {u in cal(S)'_n : |u(D^alpha f_j)| < epsilon} \
    U_2 & = inter.big_(j=1)^m {u in cal(S)'_n : |u(P f_j)| < epsilon} \
    U_3 & = inter.big_(j=1)^m {u in cal(S)'_n : |u(g f_j)| < epsilon}.
  $
  Then $U_1, U_2, U_3$ are neighborhoods of $0$ in $cal(S)'_n$, and
  $
    {D^alpha u : u in U_1} & subset.eq inter.big_(j=1)^m {D^alpha u : u in cal(S)'_n, |u(D^alpha f_j)| < epsilon} \
                           & = inter.big_(j=1)^m {D^alpha u : u in cal(S)'_n, |D^alpha u(f_j)| < epsilon} subset.eq V \
          {P u : u in U_2} & = inter.big_(j=1)^m {P u : u in cal(S)'_n, |u(P f_j)| < epsilon} \
                           & = inter.big_(j=1)^m {P u : u in cal(S)'_n, |(P u)(f_j)| < epsilon} \
                           & subset.eq inter.big_(j=1)^m {u in cal(S)'_n : |u(f_j)| < epsilon} subset.eq V \
          {g u : u in U_3} & = inter.big_(j=1)^m {g u : u in cal(S)'_n, |u(g f_j)| < epsilon} \
                           & = inter.big_(j=1)^m {g u : u in cal(S)'_n, |(g u)(f_j)| < epsilon} \
                           & subset.eq inter.big_(j=1)^m {u in cal(S)'_n : |u(f_j)| < epsilon} subset.eq V
  $
  which shows that the three maps above are indeed weak\*-continuous, as required.
]

=
#problem[
  if $u in Sn'$, prove that
  $ hat(tau_x u) = e_(-x) hat(u) "  and  " hat(e_x u) = tau_x hat(u) $
]
#solution[
  Denote by $Phi$ the Fourier transform on $Sn$, and by $rho$ the reflection operator.
  Fix $x in RR^n$. Then for every $phi in Sn$
  $
    hat(tau_x u)(phi) & = (tau_x u)(Phi phi) = u(tau_(-x) Phi phi) = u(Phi^4 (tau_(-x) Phi phi)) = u(Phi^3 (e_x Phi^2 phi)) \
                      & = u(Phi rho (e_x rho phi)) = u(Phi (e_(-x) phi)) = hat(u)(e_(-x) phi) = (e_(-x) u)(phi)
  $
  and so $hat(tau_x u) = e_(-x) u$, as required.

  Also, for every $phi in Sn$
  $
    hat(e_x u)(phi) = (e_x u)(hat(phi)) = u(e_x hat(phi)) = u(hat(tau_(-x) phi)) = hat(u)(tau_(-x) phi) = (tau_x hat(u))(phi)
  $
  and so $hat(e_x u) = tau_x hat(u)$, as required.
]

=
#problem[
  Suppose $f in L^1(Rn)$, $f != 0$, $lambda$ is a complex number, and $hat(f) = lambda f$. What can you say about $lambda$?
]
#solution[
  Denote by $Phi$ the Fourier transform on $cal(S)'_n$.
  Since $f in L^1 (RR^n)$, $hat(f) = lambda f$, and $hat(f) = Phi f$ in the distributional sense, we get $Phi^k f in L^1 (RR^n)$ for every $k$, and also $Phi^k f = lambda^k f$ for every $k$.
  But $Phi^4$ is the identity, and so we get $f = lambda^4 f$, where the equality is in $cal(S)'_n$.
  Then for every $phi in cal(D)(RR^n)$
  $ integral_(RR^n) f phi dif m_n = lambda^4 integral_(RR^n) f phi dif m_n $
  Since $f != 0$, in particular there is $phi$ for which $integral_(RR^n) f phi dif m_n != 0$, and so we get $lambda^4 = 1$, that is, $lambda$ is a root of unity of order $4$.
]

=
#problem[
  Prove (a) of Theorem 7.8 directly (without using Fourier transform).
]
#solution[
  Let $f, g in Sn$.

  #claim[$f * g in C^oo (RR^n)$, and $D^alpha (f * g) = f * D^alpha g$ for every multi-index $alpha$.] <conv-smooth>
  #proof[
    There is a sequence ${phi_k}$ in $cal(D)(RR^n)$ for which $phi_k -> g$ in $Sn$.
    In particular, for every $alpha$ we have $D^alpha phi_k -> D^alpha g$ uniformly on all of $RR^n$, and in particular ${D^alpha phi_k}$ is a uniformly Cauchy sequence on $RR^n$.
    For every $k$ we have $f * phi_k in C^oo (RR^n)$, and for every $alpha$ we have $D^alpha (f * phi_k) = f * D^alpha phi_k$.
    Then for every $k, j$ and every $alpha$ we get
    $
      norm(D^alpha (f * phi_k) - D^alpha (f * phi_j))_oo &<= sup_(x in RR^n) integral_(RR^n) |f(x - y)| |D^alpha phi_k (y) - D^alpha phi_j (y)| dif m_n (y) \
      &<= norm(f)_1 norm(D^alpha phi_k - D^alpha phi_j)_oo.
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
    &<= sum_(gamma <= beta) |c_(beta gamma)| (integral_(RR^n) abs((x - y)^(beta - gamma) f(x - y))^2 dif m_n (y))^(1\/2)(integral_(RR^n) abs(y^gamma (D^alpha g)(y))^2 dif m_n (y))^(1\/2) \
    &= sum_(gamma <= beta) |c_(beta gamma)| (integral_(RR^n) abs(y^(beta - gamma) f(y))^2 dif m_n (y))^(1\/2)(integral_(RR^n) abs(y^gamma (D^alpha g)(y))^2 dif m_n (y))^(1\/2)
  $
  Let $N$ be large enough that $integral_(RR^n) (1 + abs(y)^2)^(-2N) dif m_n (y) < oo$.
  Since $f, g in Sn$, the functions $y |-> y^gamma D^alpha g(y)$ and $y |-> y^(beta - gamma) f(y)$ are in $Sn$ for every $gamma <= beta$.
  Then there is $M$ for which $abs((1 + abs(y)^2)^N y^(beta - gamma) f(y)), abs((1 + abs(y)^2)^N y^gamma (D^alpha g)(y)) < M$ for every $y$.
  That is, for every $y$ we have $abs(y^gamma (D^alpha g)(y))^2 < M^2 (1 + abs(y)^2)^(-2N)$ and also $abs(y^(beta - gamma) f(y))^2 < M^2 (1 + abs(y)^2)^(-2N)$.
  Then for every $x in RR^n$ we get
  $
    abs(x^beta (D^alpha (f * g))(x)) &<= sum_(gamma <= beta) |c_(beta gamma)| (integral_(RR^n) M^2 (1 + abs(y)^2)^(-2N) dif m_n (y))^(1\/2)(integral_(RR^n) M^2 (1 + abs(y)^2)^(-2N) dif m_n (y))^(1\/2) \
    &= sum_(gamma <= beta) |c_(beta gamma)| M^2 integral_(RR^n) (1 + abs(y)^2)^(-2N) dif m_n (y) < oo
  $
  This shows that for all multi-indices $alpha, beta$, the function $x |-> x^beta D^alpha (f * g)(x)$ is bounded.
  Now if $P(x) = sum_beta d_beta x^beta$ is any polynomial, then for every $beta$ there is $M_beta > 0$ for which
  $ sup_(x in RR^n) abs(x^beta D^alpha (f * g)(x)) <= M_beta $
  and so
  $
    sup_(x in RR^n) |P(x) D^alpha (f * g)(x)| & = sup_(x in RR^n) abs(sum_beta d_beta x^beta D^alpha (f * g)(x)) \
                                              & <= sum_beta |d_beta| sup_(x in RR^n) abs(x^beta D^alpha (f * g)(x)) \
                                              & <= sum_beta |d_beta| M_beta < oo
  $
  that is, $P dot D^alpha (f * g)$ is bounded for every $alpha$ and every $P$, and so $f * g in Sn$, as required.
]

= <ex-10>
The Fourier transform of a complex Borel measure $mu$ on #Rn is customarily defined to be the function $hat(mu)$ given by
$ hat(mu)(x) = integral_(Rn) e^(-i x dot t) dif mu(t) quad (x in Rn). $
+ #problem[
    Of course, $mu$ is also tempered distribution, and as such its Fourier transform was defined in section 7.14.
    Show that these two definitions are consistent.
  ]
  #solution[
    We need to show that for every $phi in cal(D)(Omega)$ we have $integral_(RR^n) hat(phi) dif mu = integral_(RR^n) hat(mu) phi dif m_n$, where $hat(mu)$ is defined as a function as in the exercise.
    We have
    $ integral_(RR^n) integral_(RR^n) |phi(x) e^(-i t dot x)| dif m_n (x) dif mu(t) = norm(phi)_1 mu(RR^n) < oo $
    and so by Fubini's theorem
    $
      integral_(RR^n) integral_(RR^n) phi(x) e^(-i t dot x) dif m_n (x) dif mu(t) = integral_(RR^n) integral_(RR^n) phi(x) e^(-i t dot x) dif mu(t) dif m_n (x)
    $
    and so we get
    $
      integral_(RR^n) hat(phi) dif mu & = integral_(RR^n) integral_(RR^n) phi(x) e^(-i t dot x) dif m_n (x) dif mu(t) \
                                      & = integral_(RR^n) (integral_(RR^n) e^(-i t dot x) dif mu(t)) phi(x) dif m_n (x) \
                                      & = integral_(RR^n) hat(mu)(x) phi(x) dif m_n (x)
    $
    as required.
  ]

+ #problem[
    Prove that each $hat(mu)$ is bounded.
  ]
  #solution[
    We show that $hat(mu)$ is bounded. Indeed, for every $x$
    $ |hat(mu)(x)| <= integral_(RR^n) |e^(-i x dot t)| dif mu(t) = integral_(RR^n) dif mu(t) = mu(RR^n) < oo $
    as required.
  ]

+ #problem[
    Prove that each $hat(mu)$ is uniformly continuous.
  ]
  #solution[
    We show that $hat(mu)$ is uniformly continuous.
    We have $e^(i x dot t) - 1 stretch(->)_(x -> 0) 0$, and also $|e^(i x dot t) - 1| <= 2$ for every $x, t in RR^n$, and $2 in L^1 (mu)$ since $mu(RR^n) < oo$.
    Then by the dominated convergence theorem we get
    $ integral_(RR^n) |e^(i x dot t) - 1| dif mu(t) stretch(->)_(x -> 0) 0 $
    Now let $epsilon > 0$. By what we saw, there is $delta > 0$ such that if $abs(x) < delta$ then $integral_(RR^n) |e^(i x dot t) - 1| dif mu(t) < epsilon$.
    Then for every $a, b in RR^n$, if $abs(a - b) < delta$ we get
    $
      |hat(mu)(a) - hat(mu)(b)| <= integral_(RR^n) |e^(-i a dot t) - e^(-i b dot t)| dif mu(t) = integral_(RR^n) |e^(i (b - a) dot t) - 1| dif mu(t) < epsilon
    $
    and this shows that $hat(mu)$ is uniformly continuous, as required.
  ]

=
#problem[
  Suppose $Lambda: Sn -> C(Rn)$ is continuous, linear, and $tau_x Lambda = Lambda tau_x$ for every $x in Rn$.
  Does it follow that there exists $u in Sn'$ such that
  $ Lambda phi.alt = u * phi.alt $
  for every $phi.alt in Sn$?
]
#solution[
  For every $phi in Sn$ define $u(phi) = (Lambda rho phi)(0)$.
  $rho$ is a continuous linear operator on $Sn$, and evaluation at $0$ is a continuous linear functional on $C(RR^n)$, and so $u$ is a continuous linear functional on $Sn$, that is, $u in cal(S)'_n$.
  For every $phi in Sn$ and every $x in RR^n$
  $
    (u * phi)(x) = u(tau_x rho phi) = (Lambda rho tau_x rho phi)(0) = (Lambda tau_(-x) rho rho phi)(0) = (tau_(-x) Lambda phi)(0) = (Lambda phi)(x)
  $
  and so $Lambda phi = u * phi$ for every $phi in Sn$, as required.
]

=
#solution[
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
    This shows that $norm(tau_y phi - phi)_oo <= C abs(y)$ for every $y in RR^n$.
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
    (u * h_j)(phi) & = ((u * h_j) * rho phi)(0) = (u * (h_j * rho phi))(0) = u(rho (h_j * rho phi)) \
                   & = u((rho h_j) * phi) stretch(->)_(j -> oo) u(phi)
  $
  that is, $u * h_j -> u$ in the weak\* topology of $cal(S)'_n$, as required.
]

=
#solution[
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
      d(y_1, y_2) & <= d(y_1, f(a_m)) + d(f(a_m), f(b_m)) + d(f(b_m), y_2) \
                  & < epsilon + epsilon + epsilon = 3 epsilon
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
      d(F(x_0), F(x)) & <= d(F(x_0), f(a_0)) + d(f(a_0), f(a)) + d(f(a), F(x)) \
                      & < 3 epsilon
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
        d(a_1, a_2) & <= d(a_1, x_1) + d(x_1, x_2) + d(x_2, a_2) \
                    & < d(x_1, x_2) + 2 epsilon
      $
      Then we get
      $
        d(F(x_1), F(x_2)) & <= d(F(x_1), f(a_1)) + d(f(a_1), f(a_2)) + d(f(a_2), F(x_2)) \
                          & <= d(F(x_1), f(a_1)) + d(a_1, a_2) + d(f(a_2), F(x_2)) \
                          & < epsilon + d(x_1, x_2) + 2 epsilon + epsilon = d(x_1, x_2) + 4 epsilon
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
]

=
#solution[
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
]

= <ex-15>
#solution[
  Fix $z = x + i y$.
  For every $s > 0$ and $lambda in CC$ define $g_s (lambda) = (1 - i s lambda)^(-N-1) e^(i r abs(y) lambda) f(x + lambda y)$. Then $g_s$ is entire in $CC$.
  Fix $s$.
  For every $A > 0$, let $Omega_A$ be the intersection of the open disc of radius $A$ in $CC$ with the upper half-plane.
  Then the boundary of $Omega_A$ is $[-A, A] union {A e^(i t) : 0 <= t <= pi}$.
  For $lambda in [-A, A]$ we have
  $
    |g_s (lambda)| & = |1 - i s lambda|^(-N-1) |e^(i r abs(y) lambda)| |f(x + lambda y)| \
                   & <= |1 - i s lambda|^(-N-1) = 1 / (1 + s^2 lambda^2)^((N+1)\/2) <= 1 // FIX: original exponent reads N+1/2
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
  and then we get $|g_s (A_0 e^(i t))| < 1$ for every $t in [0, pi]$. // FIX: original has t ∈ [0, 2π]
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
]

= <ex-16>
#solution[
  Put $m = m_3$ and $C = m_3 (B(0, 1))$.
  For every Borel set $E subset.eq RR^3$ define
  $ mu(E) = C^(-1) m({t x : t in [0, 1], x in E inter S^2}) $
  If ${E_n}$ is a sequence of pairwise disjoint Borel sets in $RR^3$, then
  $
    mu(union.big_(n in NN) E_n) & = C^(-1) m({t x : t in [0, 1], x in union.big_(n in NN) E_n inter S^2}) \
                                & = C^(-1) m(union.big_(n in NN) {t x : t in [0, 1], x in E_n inter S^2}) \
                                & = sum_(n in NN) C^(-1) m({t x : t in [0, 1], x in E_n inter S^2}) \
                                & = sum_(n in NN) mu(E_n)
  $
  and so $mu$ is a Borel measure.
  Clearly $mu(E) = 0$ if $E inter S^2 = emptyset$, and so $mu$ is concentrated on $S^2$.
  Also,
  $ mu(RR^3) = C^(-1) m({t x : t in [0, 1], x in S^2}) = C^(-1) m(B(0, 1)) = 1 $
  and so $mu$ is a probability measure.
  Lebesgue measure is invariant under rotations, and so if $T : RR^3 -> RR^3$ is a rotation, then
  $
    mu(T(E)) & = C^(-1) m({t x : t in [0, 1], x in T(E)}) \
             & = C^(-1) m({t T x : t in [0, 1], x in E}) \
             & = C^(-1) m(T({t x : t in [0, 1], x in E})) \
             & = C^(-1) m({t x : t in [0, 1], x in E}) \
             & = mu(E)
  $
  and so $mu$ is also invariant under rotations.

  #claim[For every Borel function $phi$ on $RR^3$ we have $integral_(RR^3) phi dif mu = C^(-1) integral_(B(0, 1)) phi(abs(t)^(-1) t) dif m(t)$.] <sphere-integral>
  #proof[
    If $E subset.eq S^2$ is a Borel set, then for every $s in B(0, 1)$ // FIX: original has t ∈ B(0, 1)
    $ chi_E (abs(s)^(-1) s) = chi_({t x : t in [0, 1], x in E}) (s) $ // FIX: original has x ∈ T(E)
    and so
    $
      integral_(S^2) chi_E dif mu & = mu(E) = C^(-1) m({t x : t in [0, 1], x in E inter S^2}) \
                                  & = C^(-1) integral_(B(0, 1)) chi_({t x : t in [0, 1], x in E}) dif m \
      // FIX: original has x ∈ T(E)
                                  & = C^(-1) integral_(B(0, 1)) chi_E (abs(t)^(-1) t) dif m(t)
    $
    Then by linearity, for every simple Borel function $phi$ supported on $S^2$
    $ integral_(S^2) phi dif mu = C^(-1) integral_(B(0, 1)) phi(abs(t)^(-1) t) dif m(t) $
    But then by the monotone convergence theorem the last equality holds for every Borel function $phi >= 0$ supported on $S^2$, and by linearity again we get that this equality holds for any Borel function $phi$ supported on $S^2$.

    Finally, if $phi$ is any Borel function on $RR^3$, then since $mu$ is concentrated on $S^2$ we get
    $
      integral_(RR^3) phi dif mu & = integral_(S^2) phi dif mu = integral_(S^2) chi_(S^2) phi dif mu \
                                 & = C^(-1) integral_(B(0, 1)) chi_(S^2) (abs(t)^(-1) t) phi(abs(t)^(-1) t) dif m(t) \
                                 & = C^(-1) integral_(B(0, 1)) phi(abs(t)^(-1) t) dif m(t)
    $
  ]

  By @ex-10, $hat(mu) in C(RR^3)$, and for every $x$
  $ hat(mu)(x) = integral_(RR^n) e^(-i x dot t) dif mu(t) $
  Fix $x$. Then since $mu$ is invariant under rotations, and since the inner product is preserved under isometries (and in particular rotations), for every rotation $T : RR^3 -> RR^3$
  $
    hat(mu)(T x) = integral_(RR^n) e^(-i T x dot t) dif mu(t) = integral_(RR^n) e^(-i T x dot T t) dif mu(t) = integral_(RR^n) e^(-i x dot t) dif mu(t) = hat(mu)(x) // FIX: original repeats the middle step twice
  $
  that is, $hat(mu)$ is also invariant under rotations.
  Then in particular, for every $x$
  $ hat(mu)(x) = hat(mu)(abs(x) e_3) = integral_(RR^n) e^(-i abs(x) t_3) dif mu(t) $
  and by @sphere-integral and passing to spherical coordinates, for every $x != 0$ we get
  $
    hat(mu)(x) &= C^(-1) integral_(B(0, 1)) e^(-i abs(x) abs(t)^(-1) t_3) dif m(t) \
    &= (2 pi)^(-3\/2) C^(-1) integral_0^1 integral_0^(2 pi) integral_0^pi r^2 sin(phi.alt) e^(-i abs(x) cos phi.alt) dif phi.alt dif theta dif r \
    &= (2 pi)^(-1\/2) C^(-1) (integral_0^1 r^2 dif r) (integral_0^pi sin(phi.alt) e^(-i abs(x) cos phi.alt) dif phi.alt) \
    &= 1/3 (2 pi)^(-1\/2) C^(-1) (e^(-i abs(x) cos pi) - e^(-i abs(x) cos 0)) / (i abs(x)) \
    &= 2/3 (2 pi)^(-1\/2) C^(-1) abs(x)^(-1) (e^(i abs(x)) - e^(-i abs(x))) / (2 i) \
    &= 2/3 (2 pi)^(-1\/2) C^(-1) (sin abs(x)) / abs(x)
  $
  But
  $
    C &= integral_(B(0, 1)) dif m = (2 pi)^(-3\/2) integral_0^1 integral_0^(2 pi) integral_0^pi r^2 sin(phi.alt) dif phi.alt dif theta dif r = (2 pi)^(-1\/2) integral_0^1 r^2 dif r integral_0^pi sin(phi.alt) dif phi.alt \
    &= 1/3 (2 pi)^(-1\/2) (-cos(pi) + cos(0)) = 2/3 (2 pi)^(-1\/2)
  $
  and so for every $x != 0$ we got $hat(mu)(x) = abs(x)^(-1) sin abs(x)$.
  Also, $hat(mu)(0) = integral_(RR^n) dif mu(t) = 1 = lim_(x -> 0) abs(x)^(-1) sin abs(x)$.

  Put $u = D_1 mu$.
  Then if $P(x) = x_1$, we have $hat(u) = hat(D_1 mu) = P hat(mu)$. // FIX: original has hat(D_1 u)
  But since $hat(mu) in C(RR^3)$, also $P hat(mu) in C(RR^3)$, and $(P hat(mu))(x) = x_1 hat(mu)(x)$.
  And so $hat(u) in C(RR^3)$, and
  $ |hat(u)(x)| = (abs(x_1) abs(sin abs(x))) / abs(x) <= abs(sin abs(x)) <= 1 $
  for every $x in RR^3$.
  For $phi in cal(D)(RR^3)$ whose support does not intersect $S^2$, we have
  $ u(phi) = - integral_(RR^3) D_1 phi dif mu = - integral_(S^2) D_1 phi dif mu = 0 $
  and so the support of $u$ is contained in $S^2$.
  So $u$ has compact support, and so we can put $f(z) = u(e_(-z))$ for every $z in CC^3$.
  Then by the Paley–Wiener theorem for distributions with compact support, $f$ is an entire function in $CC^3$, $hat(u)$ is the restriction of $f$ to $RR^n$, and in addition there is $gamma < oo$ for which $|f(z)| <= gamma (1 + abs(z))^N e^(r abs(op("Im") z))$ for every $z in CC^n$.
  Since $f = hat(u)$ on $RR^n$, we have $|f| <= 1$ on $RR^n$.
  Take $gamma_0 >= max{gamma, 1}$. Then $abs(gamma_0^(-1) f(z)) <= (1 + abs(z))^N e^(r abs(op("Im") z))$, and also $abs(gamma_0^(-1) f(x)) < |f(x)| <= 1$ for every $x in RR^n$.
  Then $gamma_0^(-1) f$ satisfies the conditions of the claim in @ex-15, and so it satisfies its conclusion, that is, $abs(gamma_0^(-1) f(z)) <= e^(r abs(op("Im") z))$ for every $z in CC^n$.
  Then $|f(z)| <= gamma_0 e^(r abs(op("Im") z))$ for every $z in CC^3$.
  So $f$ is entire and satisfies the inequality of the Paley–Wiener theorem with $N = 0$, and yet $f$ is not the Fourier transform of a distribution of order $0$ (since it is the Fourier transform of $u = D_1 mu$, which is a distribution of order $1$), as required.

  Now we find an explicit formula for $f$.
  For every $lambda_1, lambda_2 in CC without {0}$, if $lambda_1^2 = lambda_2^2$ and $lambda_1 != lambda_2$, then $lambda_1 = -lambda_2$, and then
  $
    (sin lambda_1) / lambda_1 = (sin(-lambda_2)) / (-lambda_2) = (-sin(lambda_2)) / (-lambda_2) = (sin(lambda_2)) / lambda_2
  $
  Also, the function $lambda |-> lambda^2$ from $CC without {0}$ is onto $CC without {0}$.
  So we can define a function $h : CC without {0} -> CC$ by $h(lambda^2) = lambda^(-1) sin lambda$, and we get that $h$ is well defined on all of $CC without {0}$.
  Fix $lambda in CC without {0}$ and take some $zeta$ for which $zeta^2 = lambda$. Then
  $
    h(lambda) &= (sin zeta) / zeta = (e^(i zeta) - e^(-i zeta)) / (2 i zeta) = 1 / (2 i zeta) (sum_(n=0)^oo (i zeta)^n / n! - sum_(n=0)^oo (-i zeta)^n / n!) \
    &= 1 / (2 i zeta) sum_(n=0)^oo ((i zeta)^n (1 - (-1)^n)) / n! = sum_(n=0)^oo (i zeta)^(2n) / (2n + 1)! \
    &= sum_(n=0)^oo ((-1)^n lambda^n) / (2n + 1)!
  $
  and if we also define $h(0) = 1$, then the equality between the two extreme sides is preserved, and so we get that $h$ can be represented as a power series on all of $CC$, that is, $h$ is entire.
  Define $g : CC^3 -> CC$ by $g(z) = z_1^2 + z_2^2 + z_3^2$.
  Clearly $g$ is entire in $CC^3$, and so $h compose g$ is entire in $CC^3$.
  So $z |-> z_1 h(g(z))$ is also entire in $CC^3$.
  For every $x in RR^3$
  $
    f(x) & = u(e_(-x)) = hat(u)(x) = hat(D_1 mu)(x) = x_1 hat(mu)(x) = (x_1 sin abs(x)) / abs(x) \
         & = x_1 h(abs(x)^2) = x_1 h(x_1^2 + x_2^2 + x_3^2) = x_1 h(g(x))
  $
  and so, since $f$ is also entire, we get the equality $f(z) = z_1 h(g(z))$ for every $z in CC^3$.
  So an explicit formula for $f$ is
  $ f(z) = (z_1 sin(sqrt(z_1^2 + z_2^2 + z_3^2))) / sqrt(z_1^2 + z_2^2 + z_3^2) $
  where the square root in the expression means a choice of some square root of the expression; it does not matter which one we choose (but the choice must be the same for all occurrences in the formula), the formula will work.
]

=
#solution[
  Fix $n$.
  For every $epsilon > 0$ let $H_epsilon = K + overline(B(0, epsilon))$.
  Let $h in cal(D)(RR^n)$ with support in $overline(B(0, 1))$ and $integral_(RR^n) h dif m_n = 1$.
  For every $epsilon > 0$ define $h_epsilon (x) = epsilon^(-n) h(epsilon^(-1) x)$.

  #claim[For every $epsilon > 0$, the support of $u * h_epsilon$ is contained in $H_epsilon$, and $norm(u * h_epsilon)_2 <= norm(hat(u))_oo epsilon^(-n\/2) norm(h)_2$.] <conv-estimate>
  #proof[
    The support of $h_epsilon$ is contained in $overline(B(0, epsilon))$, and so for every $x$ the support of $tau_x rho h_epsilon$ is contained in $overline(B(x, epsilon))$.
    If for some $x$ we have $(u * h_epsilon)(x) != 0$, then $u(tau_x rho h_epsilon) != 0$, and so the support of $tau_x rho h_epsilon$ intersects $K$, and so there is $y in K$ for which $abs(x - y) <= epsilon$, that is, $x in H_epsilon$. This shows that the support of $u * h_epsilon$ is contained in $H_epsilon$ for every $epsilon > 0$.

    Fix $epsilon > 0$.
    Then $hat(u * h_epsilon) = hat(h_epsilon) hat(u)$, where the equality is in the distributional sense.
    By the Paley–Wiener theorem, $hat(u) in C^oo (RR^n)$.
    And so $hat(h_epsilon) hat(u) in C^oo (RR^n)$. Then $hat(u * h_epsilon) = hat(h_epsilon) hat(u)$ as functions.
    We have $hat(h_epsilon) (t) = hat(h)(epsilon t)$, and so
    $
      norm(hat(u * h_epsilon))_2^2 &= norm(hat(h_epsilon) hat(u))_2^2 = integral_(RR^n) abs(hat(h_epsilon))^2 |hat(u)|^2 dif m_n \
      &<= norm(hat(u))_oo^2 integral_(RR^n) abs(hat(h)(epsilon t))^2 dif m_n (t) \
      &= norm(hat(u))_oo^2 epsilon^(-n) integral_(RR^n) abs(hat(h))^2 dif m_n = norm(hat(u))_oo^2 epsilon^(-n) norm(hat(h))_2^2
    $
    and by Plancherel's theorem we get $norm(hat(u * h_epsilon))_2^2 <= norm(hat(u))_oo^2 epsilon^(-n) norm(h)_2^2$.
    From the assumption that $hat(u)$ is a bounded function we get $norm(hat(u * h_epsilon))_2^2 < oo$, and so by Plancherel's theorem again we get $norm(hat(u * h_epsilon))_2^2 = norm(u * h_epsilon)_2^2$.
    So altogether $norm(u * h_epsilon)_2 <= norm(hat(u))_oo epsilon^(-n\/2) norm(h)_2$. // FIX: dropped an unfinished sentence that follows in the original ("For every ε > 0, if")
  ]

  #claim[For every $phi in cal(D)(RR^n)$ we have $|u(phi)| <= norm(hat(u))_oo norm(h)_2 liminf_(epsilon -> 0) (epsilon^(-n) integral_(H_epsilon) |phi|^2 dif m_n)^(1\/2)$.] <liminf-estimate>
  #proof[
    By @conv-estimate, for every $epsilon > 0$ and every $phi in cal(D)(RR^n)$ we get
    $
      |(u * h_epsilon)(phi)| &= abs(integral_(RR^n) (u * h_epsilon) phi dif m_n) = abs(integral_(H_epsilon) (u * h_epsilon) phi dif m_n) \
      &<= (integral_(H_epsilon) |u * h_epsilon|^2 dif m_n)^(1\/2) (integral_(H_epsilon) |phi|^2 dif m_n)^(1\/2) \
      &= (integral_(RR^n) |u * h_epsilon|^2 dif m_n)^(1\/2) (integral_(H_epsilon) |phi|^2 dif m_n)^(1\/2) \
      &= norm(u * h_epsilon)_2 (integral_(H_epsilon) |phi|^2 dif m_n)^(1\/2) \
      &<= norm(hat(u))_oo epsilon^(-n\/2) norm(h)_2 (integral_(H_epsilon) |phi|^2 dif m_n)^(1\/2) \
      &= norm(hat(u))_oo norm(h)_2 (epsilon^(-n) integral_(H_epsilon) |phi|^2 dif m_n)^(1\/2)
    $
    But $u * h_epsilon -> u$ in $cal(D)'(RR^n)$, and in particular for every $phi in cal(D)(RR^n)$
    $ u(phi) = lim_(epsilon -> 0) (u * h_epsilon)(phi) = liminf_(epsilon -> 0) (u * h_epsilon)(phi) $
    and so we get the required inequality. // FIX: the original's final inequality has liminf as ε → ∞
  ]

  All this holds for every $n$ we choose. Now we can prove the parts.

  + Suppose $n = 1$ or $n = 2$. We need to prove that if $psi in C^oo (RR^n)$ and $psi = 0$ on $K$, then $psi u = 0$.
    That is, we need to show that $u(psi phi) = 0$ for every $phi in cal(D)(RR^n)$.
    So it suffices to show that $u(phi) = 0$ for every $phi in cal(D)(RR^n)$ for which $phi = 0$ on $K$.
    Then by @liminf-estimate it suffices to show that for every such $phi$
    $ epsilon^(-n) integral_(H_epsilon) |phi|^2 dif m_n stretch(->)_(epsilon -> 0) 0 $
    and this is what we will show.

    Since all the partial derivatives of $phi$ are bounded, there is $C > 0$ for which $|phi(x) - phi(y)| <= C abs(x - y)$ for every $x, y in RR^n$.
    Then for every $epsilon > 0$ and every $x in H_epsilon$ we have $|phi(x)| <= C epsilon$.
    So for every $epsilon > 0$
    $
      epsilon^(-n) integral_(H_epsilon) |phi|^2 dif m_n &= epsilon^(-n) integral_(H_epsilon without K) |phi|^2 dif m_n <= C^2 epsilon^(2-n) m_n (H_epsilon without K) \
      &<= C^2 epsilon^(2-n) (m_n (H_epsilon) - m_n (K))
    $
    Since $n <= 2$ we get $2 - n >= 0$, and so the expression $C^2 epsilon^(2-n)$ is bounded when $epsilon in (0, 1)$.
    On the other hand, if ${epsilon_k}$ is a decreasing sequence with $epsilon_k -> 0$, then ${H_(epsilon_k)}$ is a sequence decreasing by inclusion with $inter.big_k H_(epsilon_k) = K$, and so $m_n (H_(epsilon_k)) -> m_n (K)$.
    So $m_n (H_epsilon) stretch(->)_(epsilon -> 0) m_n (K)$.
    So $C^2 epsilon^(2-n) (m_n (H_epsilon) - m_n (K)) stretch(->)_(epsilon -> 0) 0$.
    And so $epsilon^(-n) integral_(H_epsilon) |phi|^2 dif m_n stretch(->)_(epsilon -> 0) 0$, as required.

  + Suppose $n = 2$, and $P$ is a real polynomial in two variables for which $P = 0$ on $K$.
    Then by the previous part, $P u = 0$.
    Then also $hat(P u) = 0$, but $hat(P u) = P(-D) hat(u)$, and so we get that $hat(u)$ satisfies the partial differential equation $P(-D) hat(u) = 0$. // FIX: original says u (not û) satisfies the equation
    Then for example, if we take $K$ to be the unit circle and take $P(x_1, x_2) = 1 - x_1^2 - x_2^2$, then $P$ indeed vanishes on $K$, and so in this case we get the equation
    $ hat(u) + partial^2 / (partial x_1^2) hat(u) + partial^2 / (partial x_2^2) hat(u) = 0 $
    that is, $hat(u) + Delta hat(u) = 0$.

  + Put $P(x) = 1 - x_1^2 - x_2^2 - x_3^2$.
    Let $mu$ be the measure from @ex-16, that is, $mu$ is a Borel probability measure on $RR^3$ which is concentrated on $S^2$ and invariant under rotations.
    We saw in @ex-16 that in this case $hat(mu)(x) = abs(x)^(-1) sin abs(x)$ for every $x != 0$, and so $hat(mu)$ is bounded.
    If, by contradiction, the previous part holds with $n = 3$, then we get $P(-D) hat(mu) = 0$, that is, $hat(mu) + Delta hat(mu) = 0$. // FIX: original writes û for μ̂ here
    Put $f(x) = x^(-1) sin x$ for every $x in RR without {0}$. // FIX: original has R \ (0)
    Then $f'(x) = x^(-1) cos x - x^(-2) sin x$.
    Also put $g(x) = abs(x)$ for every $x in RR^3$. Then for $x != 0$ we get
    $ partial / (partial x_j) g(x) = x_j / abs(x) $
    and so by the chain rule we get
    $ partial / (partial x_j) (f compose g)(x) = (abs(x) cos abs(x) - sin abs(x)) / abs(x)^3 x_j $
    But $hat(mu) = f compose g$, and so for every $x in RR^3 without {0}$
    $ Delta hat(mu)(x) = (abs(x) cos abs(x) - sin abs(x)) / abs(x)^3 (x_1 + x_2 + x_3) $ // TODO: this sums first derivatives; Δ is the sum of second derivatives
    and so, since $hat(mu) + Delta hat(mu) = 0$, we get for every $x in RR^3 without {0}$ the equality
    $ (sin abs(x)) / abs(x) + (abs(x) cos abs(x) - sin abs(x)) / abs(x)^3 (x_1 + x_2 + x_3) = 0 $
    But if we plug in $x = (1, 0, 0)$ we get the equality $cos(1) = 0$, which is certainly false.
    So the previous part cannot hold with $n = 3$.

  + By @conv-estimate, for every $epsilon > 0$ we have $norm(u * h_epsilon)_2 <= norm(hat(u))_oo epsilon^(-1\/2) norm(h)_2$, and the support of $u * h_epsilon$ is contained in $H_epsilon$. // FIX: original says the support "is" H_ε
    In particular, $u * h_epsilon$ is a smooth function with compact support, and so $u * h_epsilon in L^1 (RR^n)$.
    So for every $epsilon > 0$ we get
    $
      abs(integral_RR f hat(u * h_epsilon) dif m_1) &= abs(integral_RR hat(f) dot (u * h_epsilon) dif m_1) = abs(integral_(H_epsilon) hat(f) dot (u * h_epsilon) dif m_1) \
      &<= (integral_(H_epsilon) |u * h_epsilon|^2 dif m_1)^(1\/2) (integral_(H_epsilon) abs(hat(f))^2 dif m_1)^(1\/2) \
      &= norm(u * h_epsilon)_2 (integral_(H_epsilon) abs(hat(f))^2 dif m_1)^(1\/2) \
      &<= norm(hat(u))_oo norm(h)_2 (epsilon^(-1) integral_(H_epsilon without K) abs(hat(f))^2 dif m_1)^(1\/2)
    $
    Also, for every $x in H_epsilon$ there is $y in K$ for which $abs(x - y) <= epsilon$, and so $abs(hat(f)(x)) = abs(hat(f)(x) - hat(f)(y)) <= C abs(x - y)^(1\/2) <= C epsilon^(1\/2)$.
    That is, for every $epsilon > 0$ we have $abs(hat(f))^2 <= C^2 epsilon$ on $H_epsilon$, and so
    $
      abs(integral_RR f hat(u * h_epsilon) dif m_1) &<= norm(hat(u))_oo norm(h)_2 (epsilon^(-1) C^2 epsilon m_1 (H_epsilon without K))^(1\/2) \
      &= norm(hat(u))_oo norm(h)_2 C (m_1 (H_epsilon) - m_1 (K))^(1\/2)
    $
    and $m_1 (H_epsilon) stretch(->)_(epsilon -> 0) m_1 (K)$, and so we got $integral_RR f hat(u * h_epsilon) dif m_1 stretch(->)_(epsilon -> 0) 0$.

    Note that for every $x$ we have $hat(h_epsilon) (x) = hat(h)(epsilon x) stretch(->)_(epsilon -> 0) hat(h)(0) = integral_RR h dif m_1 = 1$, and so
    $
      f(x) hat(u * h_epsilon) (x) = f(x) hat(h_epsilon) (x) hat(u)(x) = f(x) hat(h)(epsilon x) hat(u)(x) stretch(->)_(epsilon -> 0) f(x) hat(u)(x)
    $
    for every $x in RR$. Also,
    $
      abs(f(x) hat(u * h_epsilon) (x)) = abs(f(x) hat(h)(epsilon x) hat(u)(x)) <= |f(x)| norm(hat(u))_oo norm(hat(h))_oo
    $
    and $norm(hat(u))_oo < oo$ by the assumption, and $norm(hat(h))_oo < oo$ as the Fourier transform of an $L^1 (RR)$ function.
    Then since $f in L^1 (RR)$, by the dominated convergence theorem we get
    $ integral_RR f hat(u * h_epsilon) dif m_1 stretch(->)_(epsilon -> 0) integral_RR f hat(u) dif m_1 $
    and by the uniqueness of the limit we get $integral_RR f hat(u) dif m_1 = 0$, as required.
]

=
#solution[
  Replacing $F$ by the suggestion from the exercise will not work, since then we would get $D_i^r F = sum_(s=0)^r binom(r, s) (D_i^(r-s) chi_K) g_(i s)$ in $Omega$, and $D_i^(r-s) chi_K$ is necessarily a distribution which is not a function, and so $D_i^r F$ cannot be in $L^2 (Omega)$, and so also not in $L^2 (RR^n)$.

  One could hope that the proof still works, if we were able to show that $integral_(RR^n) y_i^(2r) abs(hat(F)(y))^2 dif m_n (y) < oo$, but this is impossible, since if that were the case then $hat(D_i^r F) in L^2 (RR^n)$, and then by Plancherel's theorem we would get $D_i^r F in L^2 (RR^n)$, in contradiction to what we just said.
  That is, $integral_(RR^n) y_i^(2r) abs(hat(F)(y))^2 dif m_n (y) = oo$, and this ruins the entire proof.
]

=
#solution[
  Let $r >= 0$ be an integer.
  Let $f$ be a function on an open set $Omega subset.eq RR^n$ such that for every $1 <= i <= n$ and $0 <= k <= r$, the distributional derivative $D_i^k f$ is a locally $L^2$ function in $Omega$.
  Fix a multi-index $alpha$ with $|alpha| <= r$.
  Let $omega$ be an open set whose closure $K$ is compact and contained in $Omega$.
  Take $psi in cal(D)(Omega)$ with $psi = 1$ on $K$, and define $F = psi f$ on $Omega$, and $F = 0$ outside $Omega$.
  In the proof of Sobolev's lemma, we saw that
  $ integral_(RR^n) (1 + abs(x))^(2r) abs(hat(F)(x))^2 dif m_n (x) < oo $ // FIX: original has |F̂(x)| without the square
  and so we get
  $
    integral_(RR^n) abs(x^alpha hat(F)(x))^2 dif m_n &<= integral_(RR^n) abs(x)^(2|alpha|) abs(hat(F)(x))^2 dif m_n <= integral_(RR^n) (1 + abs(x))^(2|alpha|) abs(hat(F)(x))^2 dif m_n \
    &<= integral_(RR^n) (1 + abs(x))^(2r) abs(hat(F)(x))^2 dif m_n < oo
  $
  That is, if we put $P(x) = x^alpha$, then we proved that $P hat(F) in L^2 (RR^n)$.
  But $P hat(F) = hat(P(D) F)$, and so $hat(D_alpha F) in L^2 (RR^n)$, and so $hat(D^alpha F) in L^2 (RR^n)$.
  By Plancherel's theorem we now get $D^alpha F in L^2 (RR^n)$.
  Since $F = f$ on $omega$, we have $D^alpha F = D^alpha f$ on $omega$ in the distributional sense (that is, $D^alpha F(phi) = D^alpha f(phi)$ for every $phi in cal(D)(omega)$).
  So in fact we showed that for every open $omega$ for which $overline(omega)$ is compact and $overline(omega) subset.eq Omega$, there is a function $g_omega in L^2 (RR^n)$ for which $g_omega = D^alpha f$ on $omega$.

  Suppose $omega, omega'$ are two such sets with $omega inter omega' != emptyset$. Then for every $phi in cal(D)(omega inter omega')$
  $ g_omega (phi) = D^alpha f(phi) = g_(omega') (phi) $
  that is, for every $phi in cal(D)(omega inter omega')$
  $ integral_(RR^n) g_omega phi dif m_n = integral_(RR^n) g_(omega') phi dif m_n $
  and so $g_omega = g_(omega')$ on $omega inter omega'$.

  Now for every $x in Omega$ fix some $r_x > 0$ for which $overline(B(x, r_x)) subset.eq Omega$, and put $omega_x = B(x, r_x)$.
  Define $g(x) = g_(omega_x) (x)$.
  For every $x in Omega$ and every $y in omega_x$ we have $y in omega_y inter omega_x$, and so $g_(omega_x) (y) = g_(omega_y) (y) = g(y)$.
  This proves that $g = g_(omega_x)$ on $omega_x$ for every $x in Omega$.
  Let $K subset.eq Omega$ be any compact set. By compactness, there is a finite set $F subset.eq K$ for which $K subset.eq union.big_(x in F) omega_x$. Then we get
  $
    integral_K |g|^2 dif m_n <= sum_(x in F) integral_(omega_x) |g|^2 dif m_n <= sum_(x in F) integral_(RR^n) abs(g_(omega_x))^2 dif m_n < oo
  $
  where in the last step we used the finiteness of $F$ and the fact that $g_(omega_x) in L^2 (RR^n)$ for every $x in Omega$.
  This shows that $g$ is locally $L^2$ in $Omega$.

  It remains to show that $g = D^alpha f$.
  Let $phi in cal(D)(Omega)$. Let $K$ be the support of $phi$, and as before take a finite $F subset.eq K$ for which $K subset.eq union.big_(x in F) omega_x$.
  Then ${omega_x : x in F} union {RR^n without K}$ is an open cover of $RR^n$.
  Let ${psi_m}$ be a locally finite partition of unity subordinate to the above cover.
  Fix $m$ for a moment. If the support of $psi_m$ is contained in $RR^n without K$, then $psi_m phi = 0$, and so
  $ integral_(RR^n) g psi_m phi dif m_n = (-1)^(|alpha|) integral_(RR^n) f D^alpha (psi_m phi) dif m_n $
  Otherwise, there is $x in F$ for which the support of $psi_m$ is contained in $omega_x$, and since $D^alpha f = g_(omega_x)$ on $omega_x$ in the distributional sense, and $g = g_(omega_x)$ on $omega_x$, we get
  $
    integral_(RR^n) g psi_m phi dif m_n &= integral_(omega_x) g psi_m phi dif m_n = integral_(omega_x) g_(omega_x) psi_m phi dif m_n = (-1)^(|alpha|) integral_(omega_x) f D^alpha (psi_m phi) dif m_n \
    &= (-1)^(|alpha|) integral_(RR^n) f D^alpha (psi_m phi) dif m_n
  $
  That is, in any case
  $ integral_(RR^n) g psi_m phi dif m_n = (-1)^(|alpha|) integral_(RR^n) f D^alpha (psi_m phi) dif m_n $
  for every $m$, and so we get
  $
    integral_(RR^n) g phi dif m_n &= sum_m integral_(RR^n) g psi_m phi dif m_n = sum_m (-1)^(|alpha|) integral_(RR^n) f D^alpha (psi_m phi) dif m_n \
    &= (-1)^(|alpha|) integral_(RR^n) f D^alpha (sum_m psi_m phi) dif m_n = (-1)^(|alpha|) integral_(RR^n) f D^alpha phi dif m_n
  $
  So we got that for every $phi in cal(D)(Omega)$
  $ integral_(RR^n) g phi dif m_n = (-1)^(|alpha|) integral_(RR^n) f D^alpha phi dif m_n $
  and so $g = D^alpha f$, as required.
]

=
#solution[
  Put $g(y) = (1 + abs(y))^(-4) (log(2 + abs(y)))^(-1)$. Then
  $
    integral_(RR^2) |g|^2 dif m_n &= integral_(RR^2) (1 / ((1 + abs(y))^4 log(2 + abs(y))))^2 dif m_n (y) \
    &<= (1 / (log 2))^2 integral_(RR^2) 1 / (1 + abs(y))^8 dif m_n (y) \
    &= 1 / (2 pi) (1 / (log 2))^2 integral_0^oo integral_0^(2 pi) r / (1 + r)^8 dif theta dif r \
    &<= (1 / (log 2))^2 integral_0^oo r / (1 + r)^8 dif r < oo
  $
  and so $g in L^2 (RR^2)$. So $Phi^4 g = g$ (where $Phi$ is the Fourier transform).
  On the other hand
  $
    integral_(RR^2) |g| dif m_n & = integral_(RR^2) 1 / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) \
                                & <= 1 / (log(2)) integral_(RR^2) 1 / (1 + abs(y))^4 dif m_n (y) \
                                & = 1 / (2 pi) 1 / (log 2) integral_0^oo integral_0^(2 pi) r / (1 + r)^4 dif theta dif r \
                                & = 1 / (log 2) integral_0^oo r / (1 + r)^4 dif r < oo
  $
  and so $g in L^1 (RR^2)$, and so also $rho g in L^1 (RR^2)$.
  But $Phi^3 g = Phi rho g$, and the Fourier transform of a function in $L^1 (RR^2)$ is always continuous, and so we get that $Phi^3 g$ is continuous.
  Put $f = Phi^3 g$. Then $hat(f) = hat(Phi^3 g) = Phi^4 g = g$. Also, by what we saw, $f in L^2 (RR^2)$ and $f$ is continuous.
  We have
  $
    integral_(RR^2) abs(abs(y)^3 hat(f)(y))^2 dif m_n (y) &= integral_(RR^2) abs(y)^6 (1 / ((1 + abs(y))^4 log(2 + abs(y))))^2 dif m_n (y) \
    &= integral_(RR^2) abs(y)^6 / ((1 + abs(y))^8 log^2 (2 + abs(y))) dif m_n (y) \
    &= 1 / (2 pi) integral_0^(2 pi) integral_0^oo r r^6 / ((1 + r)^8 log^2 (2 + r)) dif r dif theta \
    &= integral_0^oo r^7 / ((1 + r)^8 log^2 (2 + r)) dif r \
    &<= integral_0^1 r^7 / ((1 + r)^8 log^2 (2 + r)) dif r + integral_1^oo 1 / (r log^2 (2 + r)) dif r
  $
  and
  $ integral_0^1 r^7 / ((1 + r)^8 log^2 (2 + r)) dif r < oo $
  since the integrand is continuous on $[0, 1]$.
  Also, by the change of variables $s = log(2 + r)$ we get
  $
    integral_1^oo 1 / (r log^2 (2 + r)) dif r &= integral_1^oo (2 + r) / (r log^2 (2 + r)) (dif r) / (2 + r) = integral_(log 3)^oo e^s / ((e^s - 2) s^2) dif s \
    &= integral_(log 3)^oo 1 / s^2 + 2 / ((e^s - 2) s^2) dif s <= integral_(log 3)^oo 3 / s^2 dif s < oo
  $
  and so altogether $integral_(RR^2) abs(abs(y)^3 hat(f)(y))^2 dif m_n (y) < oo$, that is, $y |-> abs(y)^3 hat(f)(y)$ is in $L^2 (RR^2)$.

  For $j = 1, 2$ put $P_j (y) = y_j$.
  For every $k, j$ we have the distributional equality $hat(D_j^k f) = i P_j^k hat(f)$.
  But $hat(f)$ is a function, and so $hat(D_i^k f)$ is also a function.
  Then for every $0 <= k <= 3$ and $1 <= i <= 2$
  $
    integral_(RR^2) abs(hat(D_i^k f))^2 dif m_n &= integral_(RR^2) |P_i|^(2k) abs(hat(f))^2 dif m_n \
    &<= integral_(B(0, 1)) |P_i|^(2k) abs(hat(f))^2 dif m_n + integral_(RR^2 without B(0, 1)) abs(y)^6 abs(hat(f)(y))^2 dif m_n (y) \
    &<= integral_(B(0, 1)) |P_i|^(2k) abs(hat(f))^2 dif m_n + integral_(RR^2 without B(0, 1)) abs(abs(y)^3 hat(f)(y))^2 dif m_n (y) \
    &< oo
  $
  That is, $hat(D_i^k f) in L^2 (RR^2)$ for every $1 <= i <= 2$ and $0 <= k <= 3$.
  Then by Plancherel's theorem, $D_i^k f in L^2 (RR^2)$ for every $1 <= i <= 2$ and $0 <= k <= 3$.
  Then by Sobolev's lemma we get $f in C^((1)) (RR^2)$, as required.

  Now we show that $f in.not C^((2)) (RR^2)$.
  From the definition of $f$ we get $f = Phi^3 g = rho Phi g$, and so for almost every $x$ // FIX: original has RΦg
  $ f(x) = Phi g(-x) = integral_(RR^2) e^(i x dot y) / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) $
  For every $y in RR^2$ and $h in RR without {0}$ put $phi_h (y) = 2 h^(-2) (cos(h y_1) - 1)$.
  Then for every $h in RR without {0}$ we get
  $
    (f(h, 0) + f(-h, 0) - 2 f(0, 0)) / h^2 &= integral_(RR^2) (e^(i h y_1) + e^(-i h y_1) - 2) / (h^2 (1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) \
    &= integral_(RR^2) (phi_h (y)) / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y)
  $
  Also, by L'Hôpital's rule we get
  $
    lim_(h -> 0) phi_h (y) = lim_(h -> 0) (-y_1 sin(h y_1)) / h = lim_(h -> 0) (-y_1^2 cos(h y_1)) = -y_1^2
  $
  for every $y in RR^2$.
  Also, for every $y in RR^2$ and $h in RR without {0}$ we have $cos(h y_1) - 1 <= 0$ and $h^2 > 0$, and so
  $ phi_h (y) = (2 (cos(h y_1) - 1)) / h^2 <= 0 $
  that is, $-phi_h >= 0$. Then by Fatou's lemma we get
  $
    liminf_(h -> 0) integral_(RR^2) (-phi_h (y)) / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) &>= integral_(RR^2) (liminf_(h -> 0) (-phi_h (y))) / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) \
    &= integral_(RR^2) (lim_(h -> 0) (-phi_h (y))) / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) \
    &= integral_(RR^2) y_1^2 / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y)
  $
  By symmetry considerations (or by a simple change of variables)
  $
    integral_(RR^2) y_1^2 / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) = integral_(RR^2) y_2^2 / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y)
  $
  and so
  $
    integral_(RR^2) y_1^2 / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) &= 1/2 integral_(RR^2) (y_1^2 + y_2^2) / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) \
    &= 1/2 integral_(RR^2) abs(y)^2 / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) \
    &= 1/2 dot 1 / (2 pi) integral_0^(2 pi) integral_0^oo r r^2 / ((1 + r)^4 log(2 + r)) dif r dif theta \
    &= 1/2 integral_0^oo r^3 / ((1 + r)^4 log(2 + r)) dif r \
    &>= 1/2 integral_1^oo 1 / (r log(2 + r)) dif r \
    &= 1/2 integral_(log 3)^oo e^s / ((e^s - 2) s) dif s \
    &= 1/2 (integral_(log 3)^oo 1 / s dif s + integral_(log 3)^oo 2 / ((e^s - 2) s) dif s) \
    &>= 1/2 integral_(log 3)^oo 1 / s dif s = oo
  $
  and so altogether we got
  $
    liminf_(h -> 0) integral_(RR^2) (-phi_h (y)) / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) >= integral_(RR^2) y_1^2 / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) = oo
  $
  and so
  $ integral_(RR^2) (-phi_h (y)) / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) stretch(->)_(h -> 0) oo $
  and so
  $
    (f(h, 0) + f(-h, 0) - 2 f(0, 0)) / h^2 = integral_(RR^2) (phi_h (y)) / ((1 + abs(y))^4 log(2 + abs(y))) dif m_n (y) stretch(->)_(h -> 0) -oo
  $
  as required.

  Now if, by contradiction, $f in C^((2)) (RR^2)$, then L'Hôpital's rule gives
  $
    lim_(h -> 0) (f(h, 0) + f(-h, 0) - 2 f(0, 0)) / h^2 &= lim_(h -> 0) (D_1 f(h, 0) + D_1 f(-h, 0) - 2 D_1 f(0, 0)) / (2 h) \
    &= lim_(h -> 0) (D_1^2 f(h, 0) + D_1^2 f(-h, 0) - 2 D_1^2 f(0, 0)) / 2 \
    &= (D_1^2 f(0, 0) + D_1^2 f(0, 0) - 2 D_1^2 f(0, 0)) / 2 = 0
  $
  in contradiction to what we just saw.
  So indeed $f in.not C^((2)) (RR^2)$, as required.
]
