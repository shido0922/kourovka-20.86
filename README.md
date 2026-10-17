# A counterexample to Kourovka Notebook Problem 20.86

**A negative answer to Problem 20.86 (proposed by P. Schmid) in the Kourovka Notebook No. 21: the inequality $`\ell^p \ge k^{p-1}`$ fails for $`p = 7`$, already for a solvable group of order $`2^{21} \cdot 7^3`$.**

Shido Tamaki, October 2026. Not peer reviewed.

> **How this was produced (AI disclosure).**
> The counterexample was found by Claude, an AI model made by Anthropic (Claude Opus 5.5), in a survey of open problems that Shido Tamaki initiated and directed in October 2026. The proof and the first computer checks were also written by Claude Opus 5.5. An independent review of the proof, with a separate re-implementation of all computations (the file [`verify.py`](verify.py)) and the Lean file [`Kourovka2086.lean`](Kourovka2086.lean), was done by another Claude model (Claude Fable 5.1). This write-up was also drafted by Claude.
> Only part of the argument is formally verified in Lean (see Section 5); the rest rests on the hand proof below and on computer checks (linear algebra over $`\mathbb{F}_8`$, and a brute force over all elements of $`G`$), done by two separately written programs.
>
> **TODO (Shido): what I checked myself, in my own words.**

## 1. The problem

Let $`G`$ be a finite group and $`p`$ a prime such that the number $`s_p(G)`$ of Sylow *p*-subgroups of $`G`$ is greater than $`1`$; write $`s_p(G) = 1 + kp`$. Let $`G_p`$ be the set of *p*-elements of $`G`$ (elements whose order is a power of $`p`$, including the identity). By a theorem of Frobenius, $`\left\lvert G_p \right\rvert = \left\lvert P \right\rvert \cdot f_p(G)`$ for a positive integer $`f_p(G)`$, where $`P`$ is a Sylow *p*-subgroup, and $`f_p(G) = 1 + \ell (p - 1)`$ for an integer $`\ell`$. Problem 20.86 asks: "Is always $`\ell^p \ge k^{p-1}`$?" It also recalls that P. Gheri proved $`f_p(G)^p \ge s_p(G)^{p-1}`$ for *p*-solvable $`G`$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), *Unsolved Problems in Group Theory. The Kourovka Notebook* No. 21, arXiv:1401.0300 (version 48, 6 October 2026), Problem 20.86 (page 169). In that version, and in the editors' current file of October 2026, the problem carries no mark (it is open).

## 2. Result

**Theorem.** Let $`\omega`$ be a generator of the multiplicative group of the field $`\mathbb{F}_8`$, let $`V = \mathbb{F}_8^7`$ with basis $`e_0, \dots, e_6`$ (indices mod 7), and let $`x, y \in GL_7(\mathbb{F}_8)`$ be given by $`x e_i = \omega^i e_i`$ and $`y e_i = e_{i+1}`$. Put $`E = \langle x, y \rangle`$ and $`G = V \rtimes E`$. Then $`E`$ is extraspecial of order $`7^3`$ and exponent $`7`$, $`G`$ is solvable of order $`2^{21} \cdot 7^3 = 719323136`$, and for $`p = 7`$:

| quantity | value |
|---|---|
| $`s_7(G)`$ | $`2^{21} = 2097152 = 1 + 7 \cdot 299593`$ |
| $`k`$ | $`299593 = (2^{21} - 1)/7`$ |
| $`\left\lvert G_7 \right\rvert`$ | $`1 + 6 \cdot 8^7 + 336 \cdot 8^6 = 100663297 = 343 \cdot 293479`$ |
| $`f_7(G)`$ | $`293479 = 1 + 6 \cdot 48913`$ |
| $`\ell`$ | $`48913 = (2^{24} - 57)/343`$ |
| $`\ell^7`$ | $`669838495472739697494750319599217`$ |
| $`k^6`$ | $`723086029984186130422176990254449`$ |
| $`\ell^7 / k^6`$ | $`0.92636\ldots < 1`$ |

So $`\ell^7 < k^6`$, and the answer to Problem 20.86 is **no**, even for solvable groups (here also $`O_7(G) = 1`$).

**Remarks.**

1. Gheri's inequality holds for this group, as it must since $`G`$ is solvable: $`f_7^7 / s_7^6 = 293479^7 / 2^{126} = 2.204\ldots`$. The two inequalities are related by the exact identity
$$\frac{\ell^p}{k^{p-1}} = \frac{f_p^p}{s_p^{p-1}} \cdot \left(1 - \frac{1}{f_p}\right)^p \left(1 - \frac{1}{s_p}\right)^{-(p-1)} \cdot \frac{p^{p-1}}{(p-1)^p},$$
and the last factor is less than $`1`$ for $`p \ge 5`$ (it is $`0.420\ldots`$ for $`p = 7`$), while the middle factor is less than $`1`$ because $`f_p \le s_p - 1`$ (Remark 3). So for $`p \ge 5`$ the inequality asked about in 20.86 implies Gheri's, and groups that are close to equality in Gheri's inequality are natural candidates for counterexamples. In the language of W. Knapp and P. Schmid (2024), $`G`$ is 7-nilpotent with a Sylow subgroup of exponent $`7`$, the case of equality $`\hat f_7 = s_7^{6/7} = 2^{18}`$ in their Lemma 6 (where $`\hat f_p`$ is their geometric-mean version of $`f_p`$).
2. The result is consistent with Theorem 1 of Knapp and Schmid (2024): $`\ell < kp/(p-1)`$ holds, and $`\ell < k`$ is allowed because the Sylow 7-subgroup $`P`$ is not strongly non-redundant: the set $`\hat P`$ of elements of $`P`$ that lie in some other Sylow 7-subgroup has $`337 > 49 = \left\lvert P \right\rvert / 7`$ elements.
3. The bound $`f_p(G) = 1 + \ell(p-1) \le k - (k-1)/(p-1)`$ stated in the problem text appears to contain a misprint: for $`G = S_3`$ and $`p = 2`$ one has $`k = 1`$ and $`f_2 = 2`$, while the right-hand side is $`1`$. The bound $`\ell < kp/(p-1)`$ of Knapp and Schmid (equivalently $`f_p(G) \le s_p(G) - 1`$) does hold. This does not affect the question.

## 3. Proof

The only theorem used is Sylow's theorem (the number of Sylow *p*-subgroups is the index of the normalizer of one of them). A *p*-element is an element whose order is a power of $`p`$.

### 3.1 The field $`\mathbb{F}_8`$

$`\mathbb{F}_8`$ is the field with 8 elements, for example $`\mathbb{F}_2[t]/(t^3 + t + 1)`$. Its multiplicative group has prime order $`7`$, so every element other than $`1`$ has order $`7`$; let $`\omega`$ be one of them. Then $`\omega^0, \dots, \omega^6`$ are distinct and make up $`\mathbb{F}_8^\times`$. Since the characteristic is $`2`$, we have $`7 = 1`$ in $`\mathbb{F}_8`$. For $`\zeta \in \mathbb{F}_8^\times`$ put $`\sigma(\zeta) = 1 + \zeta + \dots + \zeta^6`$; then $`\sigma(1) = 7 = 1`$, and $`\sigma(\zeta) = 0`$ for $`\zeta \ne 1`$ because $`(\zeta - 1)\sigma(\zeta) = \zeta^7 - 1 = 0`$.

### 3.2 The group $`E`$

From $`x e_i = \omega^i e_i`$ and $`y e_i = e_{i+1}`$ we get $`xy = \omega\, yx`$, so $`x y x^{-1} y^{-1} = \omega I`$ is a scalar matrix. For $`a, b, c \in \mathbb{Z}/7`$ put $`g(a, b, c) = \omega^c x^a y^b`$. Then
$$g(a, b, c)\, e_i = \omega^{c + a(i + b)}\, e_{i+b}, \qquad g(a, b, c)\, g(a', b', c') = g(a + a',\ b + b',\ c + c' - b a'),$$
using $`y^b x^{a'} = \omega^{-a'b} x^{a'} y^b`$.

- *Order.* The 343 elements $`g(a, b, c)`$ form a set closed under multiplication that contains $`I`$, $`x`$ and $`y`$; a finite set closed under multiplication is a group, and it lies in $`\langle x, y \rangle`$ because $`\omega I = x y x^{-1} y^{-1}`$. So $`E = \lbrace g(a, b, c) \rbrace`$. These elements are distinct: from the matrix one reads off $`b`$ (the image of $`e_0`$), then $`a`$ (the ratio $`\omega^a`$ of two coefficients), then $`c`$. Hence $`\left\lvert E \right\rvert = 7^3`$.
- *Exponent 7.* By induction on $`n`$, $`g^n e_i = \omega^{nc + a(ni + b\, n(n+1)/2)} e_{i + nb}`$ for $`g = g(a, b, c)`$. For $`n = 7`$ the exponent $`7c + 7ai + 28ab`$ is $`0`$ mod 7 and $`i + 7b \equiv i`$, so $`g^7 = I`$. (This uses that $`7`$ is odd.)
- *Centre.* By the multiplication rule, $`g(a, b, c)`$ and $`g(a', b', c')`$ commute if and only if $`b a' \equiv b' a \pmod 7`$. Taking $`(a', b') = (1, 0)`$ and $`(0, 1)`$ shows that the centre is $`Z(E) = \lbrace \omega^c I \rbrace`$, of order $`7`$. The map $`g(a, b, c) \mapsto (a, b)`$ is a homomorphism onto $`(\mathbb{Z}/7)^2`$ with kernel $`Z(E)`$, so $`E' \le Z(E)`$, and $`E' = Z(E)`$ because $`x y x^{-1} y^{-1} = \omega I`$. As $`E`$ has exponent $`7`$, $`\Phi(E) = E' E^7 = E' = Z(E)`$. Thus $`E`$ is extraspecial of order $`7^3`$ and exponent $`7`$.
- *Irreducibility and no fixed points.* If $`U \ne 0`$ is an *E*-invariant subspace and $`0 \ne u = \sum_i u_i e_i \in U`$, then with the Lagrange polynomials $`L_j(t) = \prod_{i \ne j} (t - \omega^i)/(\omega^j - \omega^i)`$ we get $`L_j(x) u = u_j e_j \in U`$, so some $`e_j \in U`$, and applying $`y`$ repeatedly gives $`U = V`$. Moreover $`C_V(E) = 0`$: if $`xv = v`$ then $`v = v_0 e_0`$, and $`yv = v`$ then forces $`v_0 = 0`$.

### 3.3 The number of Sylow 7-subgroups

$`G = V \rtimes E`$ is the set of pairs $`(v, a)`$ with $`(v, a)(u, b) = (v + au,\ ab)`$. The subgroup $`E_0 = \lbrace (0, a) \rbrace`$ has order $`7^3`$, the full 7-part of $`\left\lvert G \right\rvert = 2^{21} \cdot 7^3`$, so it is a Sylow 7-subgroup. Since $`(v, a) = (v, I)(0, a)`$ and $`(0, a) \in E_0`$, the element $`(v, a)`$ normalizes $`E_0`$ if and only if $`(v, I)`$ does. Now $`(v, I)(0, b)(v, I)^{-1} = (v - bv,\ b)`$ lies in $`E_0`$ if and only if $`bv = v`$; this holds for all $`b \in E`$ if and only if $`v \in C_V(E) = 0`$. Hence $`N_G(E_0) = E_0`$ and, by Sylow's theorem, $`s_7(G) = \left\lvert G : E_0 \right\rvert = 8^7 = 2^{21}`$. Since $`2^{21} - 1 = 7 \cdot 299593`$, we get $`k = 299593`$.

### 3.4 Which elements are 7-elements

By induction, $`(v, a)^n = (v + av + \dots + a^{n-1} v,\ a^n)`$, so $`(v, a)^7 = (N_a v,\ I)`$ with $`N_a = I + a + \dots + a^6`$. In characteristic $`2`$ we have $`(u, I)^2 = (0, I)`$, so every element has order dividing $`14`$, and $`(v, a)`$ is a 7-element if and only if $`(v, a)^7 = (0, I)`$, that is, $`N_a v = 0`$. Therefore
$$\left\lvert G_7 \right\rvert = \sum_{a \in E} \left\lvert \ker N_a \right\rvert.$$

### 3.5 The kernels of $`N_a`$

- $`a = I`$ (one element): $`N_I = 7I = I`$, so $`\ker N_I = 0`$. Contribution $`1`$.
- $`a = \omega^c I`$ with $`c \ne 0`$ (six elements): $`N_a = \sigma(\omega^c) I = 0`$, so $`\ker N_a = V`$. Contribution $`8^7`$ each.
- $`a`$ not central, which is the case for $`343 - 7 = 336`$ elements: since $`a^7 = I`$ and $`t^7 - 1 = \prod_{j=0}^{6} (t - \omega^j)`$ has distinct roots in $`\mathbb{F}_8`$, $`a`$ is diagonalizable with eigenvalues among $`\omega^0, \dots, \omega^6`$. As $`a`$ is not central, there is $`h \in E`$ with $`h a h^{-1} = \omega^m a`$ for some $`m \not\equiv 0 \pmod 7`$ (by the multiplication rule, $`h a h^{-1} a^{-1}`$ is a scalar $`\omega^m`$, and $`m \ne 0`$ for a suitable $`h`$). Conjugate matrices have the same eigenvalues with the same multiplicities, so the multiset of eigenvalues of $`a`$ is invariant under multiplication by $`\omega^m`$; since $`\omega^m`$ generates $`\mathbb{F}_8^\times`$, all seven eigenvalues $`\omega^0, \dots, \omega^6`$ occur with the same multiplicity, which must be $`1`$. On the eigenspace for $`\omega^j`$, $`N_a`$ acts as $`\sigma(\omega^j)`$, which is $`1`$ for $`j = 0`$ and $`0`$ otherwise. Hence $`\ker N_a`$ is the sum of six one-dimensional eigenspaces and $`\left\lvert \ker N_a \right\rvert = 8^6`$.

### 3.6 The count

$$\left\lvert G_7 \right\rvert = 1 + 6 \cdot 8^7 + 336 \cdot 8^6 = 100663297 = 343 \cdot 293479,$$
so $`f_7(G) = 293479 = 1 + 6 \cdot 48913`$ and $`\ell = 48913`$. In closed form, $`k = (8^7 - 1)/7`$ and $`\ell = (8^8 - 57)/7^3`$.

### 3.7 The inequality

With exact integers, $`\ell^7 = 669838495472739697494750319599217 < 723086029984186130422176990254449 = k^6`$. A check by hand: $`\ell < 2^{24}/7^3`$ and $`k^6 = 2^{126}(1 - 2^{-21})^6 / 7^6`$, so
$$\frac{\ell^7}{k^6} < \frac{2^{42}}{7^{15}} \cdot \left(1 - 2^{-21}\right)^{-6} < 0.93 \cdot 1.01 < 1,$$
since $`2^{42} = 4398046511104 < 0.93 \cdot 7^{15} = 0.93 \cdot 4747561509943`$ and $`(1 - 2^{-21})^{-6} \le 1/(1 - 6 \cdot 2^{-21}) < 1.01`$. $`\blacksquare`$

## 4. A family, and other primes

The same construction works for any odd prime $`p`$ and any prime power $`Q \equiv 1 \pmod p`$: take $`V = \mathbb{F}_Q^p`$, $`\omega`$ a primitive *p*-th root of unity in $`\mathbb{F}_Q`$, the same $`x`$ and $`y`$, and $`G = V \rtimes E`$ with $`E \cong p^{1+2}_+`$. The proof above goes through with $`7`$ replaced by $`p`$ and $`8`$ by $`Q`$. Only three points change: the exponent of $`E`$ is $`p`$ because $`p(p+1)/2 \equiv 0 \pmod p`$ for odd $`p`$; $`N_I = pI`$ is invertible because the characteristic of $`\mathbb{F}_Q`$ is not $`p`$; and $`(v, a)`$ is a *p*-element if and only if $`N_a v = 0`$, because the order of every element divides $`p`$ times the characteristic. This gives
$$s_p = Q^p, \qquad k = \frac{Q^p - 1}{p}, \qquad \left\lvert G_p \right\rvert = 1 + (p-1) Q^p + (p^3 - p) Q^{p-1}, \qquad \ell = \frac{Q^p + p(p+1) Q^{p-1} - (p^2 + p + 1)}{p^3}.$$
These formulas were also checked by brute force for $`(p, Q) = (3, 4), (3, 7), (5, 11)`$ and $`(7, 8)`$.

- Within this family, the inequality $`\ell^p \ge k^{p-1}`$ fails for the primes $`p \le 260`$ in the list $`7, 23, 29, 31, 41, 53, 83, 89, 113, 127, 131, 139, 163, 173, 179, 191, 193, 199, 233, 239, 251`$ (computed with exact integers), and never fails for $`p = 3`$ or $`p = 5`$.
- It fails for every Mersenne prime $`p \ge 7`$ (take $`Q = p + 1`$), and for every prime $`p \ge 23`$ such that $`2p + 1`$ is a prime power (take $`Q = 2p + 1`$). So it fails for infinitely many $`p`$ if there are infinitely many Mersenne primes or infinitely many Sophie Germain primes; both are open problems.
- For $`p = 7`$, $`Q = 8`$ is the only member of the family that fails.

## 5. What is verified, and how

| claim | hand proof | computer ([`verify.py`](verify.py)) | Lean ([`Kourovka2086.lean`](Kourovka2086.lean)) |
|---|---|---|---|
| $`E`$ is extraspecial of order $`7^3`$ and exponent $`7`$ | 3.2 | part B: $`E`$ generated as matrices over $`\mathbb{F}_8`$ | yes, for the abstract group with the multiplication rule of 3.2 (order, exponent, centre, commutators) |
| $`E`$ is irreducible, $`C_V(E) = 0`$ | 3.2 | part B | no |
| $`s_7(G) = 2^{21}`$ | 3.3 | parts B and D (conjugates of $`E_0`$ counted directly) | arithmetic $`2^{21} = 1 + 7 \cdot 299593`$ only |
| $`\left\lvert G_7 \right\rvert = 100663297`$ | 3.4 to 3.6 | part C (kernels by linear algebra) and part D (all $`7.2 \cdot 10^8`$ elements, using only the group law) | arithmetic only |
| $`\ell^7 < k^6`$ | 3.7 | part E (exact integers) | yes (`main_inequality`) |
| the family | 4 | parts F (brute force for small $`(p, Q)`$) and G (exact integers, $`p \le 260`$) | the algebraic identity only |

- The Lean file uses no `sorry` and no `native_decide`; `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`. It does **not** formalize the action of $`E`$ on $`V`$, the Sylow count or the count of 7-elements.
- No check with GAP or Magma has been done.
- [`verify.py`](verify.py) needs Python 3 and numpy; the brute force over all elements of $`G`$ (part D) takes a few minutes. Its output is in [`verify_out.txt`](verify_out.txt).

## 6. Questions that remain open

- Does $`\ell^p \ge k^{p-1}`$ hold for $`p = 3`$ and $`p = 5`$? (The family above never fails there.)
- What is the smallest counterexample for $`p = 7`$? (Within groups $`V \rtimes P`$ with $`V`$ elementary abelian of order prime to $`7`$ and $`P`$ a 7-group acting faithfully, the example above appears to be the smallest; this was not proved.)
- Does Gheri's inequality $`f_p(G)^p \ge s_p(G)^{p-1}`$ hold for all finite groups? The example says nothing about this, since it is solvable.

## References

1. E. I. Khukhro and V. D. Mazurov (eds.), *Unsolved Problems in Group Theory. The Kourovka Notebook* No. 21, arXiv:1401.0300 (v48, 2026).
2. P. Gheri, *On the number of p-elements in a finite group*, Ann. Mat. Pura Appl. (4) 200 (2021), 1231–1243, doi:10.1007/s10231-020-01035-9.
3. W. Knapp and P. Schmid, *Sylow intersections and Frobenius ratios*, Arch. Math. 123 (2024), 9–17, doi:10.1007/s00013-024-01995-x.
4. W. Knapp and P. Schmid, *Some small Sylow numbers*, J. Group Theory 29 (2026), 223–236, doi:10.1515/jgth-2025-0052.
