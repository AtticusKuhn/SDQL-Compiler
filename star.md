# Kleene Star


The Kleene Star A^* : T -> T is defined to be the function which statisfies the following equations (in a given
semi-ring):

A^* = A^* * A + 1
A^* = 1 + A + A*A + A*A*A + ...

# Examples of Semi-rings and their respective Kleene Star operation.
| Name                | Type            | add | multiply | star    |
|---------------------|-----------------|-----|----------|---------|
| real sum-product    | Reals           | +   | *        | 1/(1-x) |
| int  sum-product    | Int             | +   | *        |         |
| nat     sum-product | Nat             | +   | *        |         |
| min-product         | (0, infty]      | min | *        |         |
| max-product         | [0, infty)      | max | *        |         |
| min-sum             | (-infty, infty) | min | +        |         |
| max-sum             | [-infty, infty) | max | +        |         |
| max-min             | [-infty, infty] | max | min      |         |
| boolean             | {T, F}          | or  | and      |         |

| Name | Type | add ($+$) | multiply ($\cdot$) | star ($a^*$) |
| :--- | :--- | :--- | :--- | :--- |
| **Real sum-product** | $\mathbb{R}$ | $+$ | $\times$ | $1/(1-a)$ *(if $|a|<1$)* |
| **Int sum-product** | $\mathbb{Z}$ | $+$ | $\times$ | *Undefined (Diverges)* |
| **Nat sum-product** | $\mathbb{N}$ | $+$ | $\times$ | *Undefined (Diverges)* |
| **Min-product** | $(0, \infty]$ | $\min$ | $\times$ | $1$ if $a \ge 1$; $0$ if $a < 1$ |
| **Max-product** | $[0, \infty)$ | $\max$ | $\times$ | $1$ if $a \le 1$; $\infty$ if $a > 1$ |
| **Min-sum** | $(-\infty, \infty]$ | $\min$ | $+$ | $0$ if $a \ge 0$; $-\infty$ if $a < 0$ |
| **Max-sum** | $[-\infty, \infty)$ | $\max$ | $+$ | $0$ if $a \le 0$; $\infty$ if $a > 0$ |
| **Max-min** | $[-\infty, \infty]$ | $\max$ | $\min$ | $+\infty$ (Top Element) |
| **Boolean** | $\{T, F\}$ | $\lor$ | $\land$ | $T$ (True) |


# On Reals
x^* = 1/(1 - x)

# Matrices
Kleene Algebras are closed under the formation of matrices.

If a scalar domain $T$ forms a Kleene Algebra, then the set of $n \times n$ matrices with entries in $T$, denoted as $M_n(T)$, also forms a Kleene Algebra.


> **The Matrix Star Formula**:
>
> $$
> M^* = \begin{pmatrix} A & B \\ C & D \end{pmatrix}^* = \begin{pmatrix} E^* & E^* B D^* \\ D^* C E^* & D^* + D^* C E^* B D^* \end{pmatrix}
> $$
>
> Where $E = A + B D^* C$.



# Floyd-Warshall
A quite different Kleene algebra can be used to implement the Floyd–Warshall algorithm, computing the shortest path's length for every two vertices of a weighted directed graph, by Kleene's algorithm, computing a regular expression for every two states of a deterministic finite automaton. Using the extended real number line, take a + b to be the minimum of a and b and ab to be the ordinary sum of a and b (with the sum of +∞ and −∞ being defined as +∞). a* is defined to be the real number zero for nonnegative a and −∞ for negative a. This is a Kleene algebra with zero element +∞ and one element the real number zero. A weighted directed graph can then be considered as a deterministic finite automaton, with each transition labelled by its weight. For any two graph nodes (automaton states), the regular expressions computed from Kleene's algorithm evaluates, in this particular Kleene algebra, to the shortest path length between the nodes.[8]

# Dictionaries
If the value elements with type V form a semi-ring structure, then the dictionary also
forms a semi-ring structure, referred to as a semi-ring dictionary (SD) where the addition
is point-wise, that is the values of elements with the same key are added. The elements of
an SD with 0V as values are made implicit and can be removed from the dictionary. This
means that two SDs with the same set of k_i and v_i pairings are equivalent regardless of
their 0V -valued k_js.
The multiplication dict * s, where dict is an SD with k_i and v_i as keys and values,
results in an SD with k_i as the keys, and v_i * s as the values. For the expression s *
dict, where s is not an SD and dict is an SD with keys k_i and values v_i, the result is
an SD with k_i as keys and s * v_i as values. Note that the multiplication operator is not
commutative by default.
Example 2. Consider the following two SDs: { "a"->2, "b"->3 } named as dict1 and
{ "a"->4, "c"->5 } named as dict2. The result of dict1+dict2 is { "a"->6, "b"->3,
"c"->5 }. This is because dict1 is equivalent to { "a"->2, "b"->3, "c"->0 } and dict2
is equivalent to { "a"->4, "b"->0, "c"->5 }, and element-wise addition of them results
in { "a"->2+4, "b"->3+0, "c"->0+5 }.
The result of dict1 * dict2 is { "a"->2 * dict2, "b"->3 * dict2 }. The expres-
sion 2 * dict2 is evaluated to { "a"->2*4, "c"->2*5 }. By performing similar
computations, dict1 * dict2 is evaluated to { "a"->{ "a"->8, "c"->10 }, "b"->{
"a"->12, "c"->15 } }. On the other hand, dict2 * dict1 is { "a"->4 * dict1,
"c"->5 * dict1 }. After performing similar computations, the expression is evaluated
to { "a"->{ "a"->8, "b"->12 }, "c"->{ "a"->10, "b"->15 } }.



| Semiring (⊕, ⊗) | $M^*_{ij}$ computes |
|---|---|
| (min, +) — the **tropical** semiring | Shortest path distance |
| (max, ×) — the **Viterbi** semiring | Most reliable path |
| (max, min) — the **bottleneck** semiring | Maximum-capacity path |
| (+, ×) — over reals (if it converges) | Total weight summed over all paths (related to matrix inverse $(I - M)^{-1}$) |
| (∨, ∧) — **Boolean** | Transitive closure (reachability) |

