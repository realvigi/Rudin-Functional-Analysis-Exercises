
#set document(title: "Rudin Functional Analysis Exercises")
#set heading(numbering: "I.1.a.")

#let Sn = $cal(S)_n$

= Fourier Transforms

==
Simple variable substitution gives:
$ hat(g)(t) = integral_(RR^n) g e_(-t) d m_n = integral_(RR^n) (f compose A) e_(-t) d m_n = 1/(|det A|) integral_(RR^n) f dot (e_(-t) compose A^(-1)) d m_n \
= 1/(|det A|) integral_(RR^n) f(x) e^(-i(t dot A^(-1)x)) d m_n (x) = 1/(|det A|) integral_(RR^n) f(x) e^(-i((A^(-1))^*t) dot x) d m_n (x) \
= 1/(|det A|) hat(f)((A^(-1))^*t) $

so we get $hat(g) =  |det A|^(-1) hat(f) compose (A^(-1))^*$

==
Put $Q(x) = 1+|x|^2$, and for all $N$ put 
$
p_N (f)=max_(|alpha|<=N) norm(Q^N D_alpha f)_infinity \
V_N = {f in cal(S)_n : p_N (f)<1/N} .
$
so ${V_N}$ is a local base for the topology of #Sn. \
Let $Phi: #Sn arrow #Sn$ be fourier transform, and for all N and all $f in #Sn$ put $q_N (f) = sum_(j=0)^3 p_N (Phi^j f)$.
Note that $q_N$ is a seminorm on #Sn, and that $q_N (f) = q_N (hat(f))$ for all $f in #Sn$. Also note that since $p_N$ is continuous map from #Sn to $RR$, and $Phi$ is continuous map from #Sn to itself, we get that $q_N$ is continuous from #Sn to $RR$. \
For all $N$ put $W_N = {f in #Sn : q_N (f)<N^(-1)}$. So $W_N$ is open, since $q_N$ is continuous. Additionally, $q_N (0) = 0$, so $W_N$ is a neighborhood of $0$ in #Sn, for all $N$.
We claim that ${W_N}$ is a local base for #Sn. \
In one direction, it is clear from the definition of $q_N$ that $p_N (f) <= q_N (f)$ for all $f in #Sn$, and so if $q_N (f) < N^(-1)$ then $p_N (f) < N^(-1) $. This shows that $W_N subset V_N$ for all $N$. \
On the other direction, fix $N$ and we need to show there is some $k$ for which $V_k subset W_N$. \
For $0<=j<=3$, the function $p_N compose Phi^j$ is continuous from #Sn to $(0,infinity)$. \
So for $0<=j<=3$, there is some $U_j$ neighborhood of $0$ in #Sn for $p_N (Phi^j f)< (4N)^(-1)$ for all $f in U_j$. \
Since ${V_k}$ is a local base, there is some $k$ for which $V_k subset inter.big_(j=0)^3 U_j$
