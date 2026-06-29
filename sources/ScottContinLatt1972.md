---
source_pdf: ScottContinLatt1972.pdf
ocr_method: cursor-vision-triple-merge
verification_status: draft
---

# Transcription (LLM vision OCR)

Scott, D. Continuous lattices. In: Toposes, Algebraic Geometry and Logic, edited by F. Lawvere. Springer-Verlag, LNM, vol. 274, 1972, pp. 97-136.

# CONTINUOUS LATTICES

BY

Dana Scott

## ABSTRACT

Starting from the topological point of view a certain wide class of $T_0$-spaces is introduced having a very strong extension property for continuous functions with values in these spaces. It is then shown that all such spaces are complete lattices whose lattice structure determines the topology - these are the *continuous lattices* - and every such lattice has the extension property. With this foundation the lattices are studied in detail with respect to projections, subspaces, embeddings, and constructions such as products, sums, function spaces, and inverse limits. The main result of the paper is a proof that every topological space can be embedded in a continuous lattice which is homeomorphic (and isomorphic) to its own function space. The function algebra of such spaces provides mathematical models for the Church-Curry $\lambda$-calculus.

## CONTENTS

1. Introduction
2. Injective Spaces
3. Continuous Lattices
4. Function Spaces
5. Inverse Limits

References

98

## 0. Introduction

Through a roundabout chain of mathematical events I have become interested in $T_0$-spaces, those topological spaces satisfying the weakest separation axiom to the effect that two distinct points cannot share the same system of open neighborhoods. These spaces seem to have been originally suggested by Kolmogoroff and were introduced first in Alexandroff and Hopf (1935). Subsequent topology textbooks have dutifully recorded the definition but without much enthusiasm: mainly the idea is introduced to provide exercises. In the book Čech (1966) for example, $T_0$-spaces are called *feebly semi-separated spaces*, which surely is a term expressing mild contempt. Some interest has been shown in finite $T_0$-spaces (finite $T_1$-spaces are necessarily discrete), but generally topology seems to go better under at least the Hausdorff separation axiom. The reason for this is no doubt the strong motivation we get from geometry, where points *are* points and where distinct points *can* be separated.

What I hope to show in this paper is that from a less geometric point of view $T_0$-spaces can be not only interesting but also natural. The interest for me lies in the construction of *function spaces*, and the main result is the production of a large number of $T_0$-spaces $D$ such that $D$ and $[D \to D]$ are *homeomorphic*. Here $[D \to D]$ is the space of all continuous functions from $D$ into $D$ with the topology of pointwise convergence (the product topology). It will be shown that every space can be embedded in such a space $D$, and that $D$ can be chosen to have quite strong extension properties for $D$-valued continuous functions. These properties make $D$ most convenient for applications to logic and recursive function theory, which was the author's original motivation. Some of the facts about these spaces seem to be most easily proved with the aid of some lattice theory, a circumstance that throws new light on the connections between topology and lattices. In fact, the required spaces are at the same time complete lattices whose topology is determined by the lattice structure in a special way, whence my title.

99

**1. INJECTIVE SPACES.** All spaces are $T_0$-spaces, and we begin by defining a class of spaces to be called *injective*.

**1.1 Definition.** A $T_0$-space $D$ is *injective* iff for arbitrary spaces $X$ and $Y$ if $X \subseteq Y$ as a subspace, then every continuous function $f: X \to D$ can be extended to a continuous function $\bar{f}: Y \to D$. As a diagram we have:

$$
\begin{gathered}
X \subseteq Y 
X \xrightarrow{f} D 
Y \xrightarrow{\bar{f}} D
\end{gathered}
$$

Some people will object to this terminology because I use the subspace relationship rather than a monomorphism in the category of $T_0$-spaces and continuous maps. However, only the trivial 1-point space is injective in the sense of monomorphisms in that category, and so the notion is uninteresting. If the reader prefers another terminology, I do not mind. As we shall see these spaces have very strong retraction properties.

A slightly less trivial example of an injective space is the 2-point space $\mathbb{O}$ with "points" $\bot$ and $\top$ where $\top$ is open but $\bot$ is not. (This space is sometimes called the *Sierpinski Space*.)

**1.2 Proposition.** The space $\mathbb{O}$ is injective.

**Proof:** As is obvious, the continuous maps $f: X \to \mathbb{O}$ are in a one-one correspondence with the open subsets of $X$ (consider $f^{-1}(\top)$). If $X \subseteq Y$ as a subspace, then an open subset of $X$ is the restriction of some open subset of $Y$. Thus any $f: X \to \mathbb{O}$ can be extended to $\bar{f}: Y \to \mathbb{O}$. $\square$

**1.3 Proposition.** The Cartesian product of any number of injective spaces is injective under the product topology.

**Proof:** The argument is standard. A map into the product can be projected onto each of the factors. Each of these projections can be extended. Then the separate maps can be put together again to make the required extended map into the product. $\square$

We now have a large number of injective spaces, and further examples could be found using the next fact.

**1.4 Proposition.** A retract of an injective space is injective.

**Proof:** Let $D$ be injective. By a retract of $D$ we understand a subspace $D' \subseteq D$ for which there exists a retraction map $j: D \to D'$ such that

100

$$
D' = x \in D : j(x) = x.
$$

Then if $f: X \to D'$ and $X \subseteq Y$, we have $f: X \to D$ as a continuous map also. Taking $\bar{f}: Y \to D$, we have only to form

$$
j \circ \bar{f} : Y \to D'
$$

to show that $D'$ is injective. $\square$

The relationship between arbitrary $T_0$-spaces and the injective spaces is given by the embedding theorem.

**1.5 Proposition.** Every $T_0$-space can be embedded in an injective space; in fact, in a Cartesian power of the 2-element space $\mathbb{O}$.

**Proof:** The proof is well known (cf. Čech (1966), Theorem 26B.9, p. 484.) But we give the argument for completeness sake. Let $X$ be the given space, and let $\mathfrak{O}$ be the class of open subsets of $X$. Let

$$
D = \mathbb{O}^{\mathfrak{O}}
$$

be the Cartesian power of $\mathbb{O}$. Then $D$ is injective by 1.3. Define the map $e: X \to D$ by:

$$
e(x)(U) = \begin{cases} \top & \text{if } x \in U,  \bot & \text{if } x \notin U, \end{cases}
$$

for $x \in X$ and $U \in \mathfrak{O}$. This map $e$ is continuous in view of the topology given to $\mathbb{O}$ and to $D$. The map $e$ is one-one, because $X$ is $T_0$. Finally, if $U \subseteq X$ is open, then

$$
\begin{aligned}
e(U) &= e(x) : x \in U 
&= e(x) : e(x)(U) = \top 
&= e(X) \cap t \in D : t(U) \in \top,
\end{aligned}
$$

which shows that the image $e(U)$ is open in the subspace $e(X) \subseteq D$. Therefore $e: X \to D$ is an embedding of $X$ as a subspace in $D$. $\square$

**1.6 Corollary.** The injective spaces are exactly the retracts of the Cartesian powers of $\mathbb{O}$.

**Proof:** Such a retract is injective by 1.4. If $D$ is injective, then it is (homeomorphic to) a subspace of a power of $\mathbb{O}$. But since $D$ is injective the identity function on the subspace to itself can be extended to the whole of the power of $\mathbb{O}$ providing the required retraction. $\square$

**1.7 Corollary.** A space is injective iff it is a retract of every space of which it is a subspace.

101

**Proof:** As in the proof of 1.6, this property is obvious for injective spaces. But in view of 1.5 every such space is a retract of a power of $\mathbb{O}$ and hence is injective. $\square$

As a result of these very elementary considerations, the injective spaces could be called *absolute retracts*, if one remembers to modify the standard definitions by using *arbitrary* subspaces rather than just *closed* subspaces. Note too that it is easy to show that the only continuous maps $e: X \to Y$ for which the extension property

$$
\begin{gathered}
X \xrightarrow{e} Y 
X \xrightarrow{f} \mathbb{O} 
Y \xrightarrow{\bar{f}} \mathbb{O}
\end{gathered}
$$

could hold for *all* continuous $f: X \to \mathbb{O}$ are embeddings as subspaces.

Thus it would seem that we have a reasonably good initial grasp of the notion of injective spaces, but further constructions are considerably facilitated by the introduction of the lattice structure.

**2. CONTINUOUS LATTICES.** Every $T_0$-space becomes a partially ordered set under the definition:

$$
x \sqsubseteq y \text{ iff whenever } x \in U \text{ and } U \text{ is open, then } y \in U.
$$

Indeed, though this relation is reflexive and transitive, the condition that it be *antisymmetric* is exactly equivalent to the $T_0$-axiom.

In the converse direction, every partially ordered set $\langle X, \sqsubseteq \rangle$ can be so obtained, for we have only to define $U \subseteq X$ as being open if it satisfies the condition:

(i) whenever $x \in U$ and $x \sqsubseteq y$, then $y \in U$.

The axioms for partial order make $X$ a $T_0$-space, because for any $y \in X$ the set

$$
x \in X : x \not\sqsubseteq y
$$

is open. This connection is not very interesting, however.

What *is* interesting in topological spaces is *convergence* and the properties of *limit points*. We shall discuss limits in terms of *nets*, in particular in terms of *monotone nets*. A monotone net in a $T_0$-space $X$ is a function

$$
x : I \to X
$$

102

where $\langle I, \le \rangle$ is a directed set and where $i \le j$ implies $x_i \sqsubseteq x_j$ for all $i, j \in I$. In a $T_1$-space a monotone net is constant (hence, uninteresting) because the $\sqsubseteq$-relation is the identity. As usual (cf. Kelley (1955), p.66) we say that a net $x$ *converges* to an element $y$ iff whenever $U$ is open and $y \in U$, then for some $i \in I$ we have $x_j \in U$ for all $j \ge i$. Note that a monotone net $x$ converges to each of its terms $x_i$. Suppose that a monotone net $x$ converges to an element $y$ which is an upper bound to all the terms of $x$. Then $y$ must be the *least upper bound*, which we write as:

$$
y = \bigsqcup x_i : i \in I.
$$

To see this, assume that $z$ is any other upper bound with $x_i \sqsubseteq z$ for all $i \in I$. If $U$ is open and $y \in U$, then $x_i \in U$ for some $i \in I$. But then $z \in U$, and so $y \sqsubseteq z$ follows.

We shall find that most of the facts about the topology of the spaces we are concerned with here can be expressed in terms of least upper bounds (lubs). It is not always the case, however, that lubs are limits. Thus, for a partially ordered set $X$, we impose a further restriction on its topology beyond condition (i) for saying when a subset $U$ is open:

(ii) whenever $S \subseteq X$ is *directed*, $\bigsqcup S$ exists, and $\bigsqcup S \in U$, then $S \cap U \neq \emptyset$.

By a directed subset of $X$ we of course mean that it is directed in the sense of the partial ordering $\sqsubseteq$. Note that in this paper directed sets are always *non-empty*. The sets satisfying (i) and (ii) form the *induced topology* on a partially ordered set $X$, which is still a $T_0$-space because the sets $x \in X : x \not\sqsubseteq y$ remain open even in the sense of (ii). Obviously a directed set $S \subseteq X$ can be regarded as a net, and now in view of (ii) it follows that $S$ converges to $\bigsqcup S$ — if this lub exists. We can summarize this discussion as follows.

**2.1 Proposition.** *In a partially ordered set $X$ with the induced topology, a monotone net $x : I \to X$ with a least upper bound converges to an element $y \in X$ iff*

$$
y \sqsubseteq \bigsqcup x_i : i \in I.
$$

$\square$

Our main interest will lie with those partially ordered sets in which every subset has a lub: namely, *complete lattices*. If $D$ is such a space we write $\bot = \bigsqcup \emptyset$ and $\top = \bigsqcup D$ for the smallest and largest elements (read: bottom and top). As is well known, greatest lower bounds must exist, for:

$$
\sqcap S = \bigsqcup x \in D : x \sqsubseteq y \text{ for all } y \in S
$$

gives the definition.

Given a complete lattice $D$ we define

103

$$
x \ll y \text{ iff } y \in \text{Int}z \in D : x \sqsubseteq z,
$$

where the interior is taken in the sense of the induced topology. The relation $x \ll y$ behaves somewhat like a strict ordering relation; at least its meaning is clearly that $y$ should be definitely larger than $x$ in the partial ordering. Such a relation has many pleasant properties.

The primary purpose of introducing it is to provide a simple definition for the kind of spaces that are most useful to us. We first mention the most elementary features of this relation.

**2.2 Proposition.** In a complete lattice $D$ we have:

(i) $\bot \ll x$;

(ii) $x \ll z$ and $y \ll z$ imply $x \sqcup y \ll z$;

(iii) $x \ll y \sqsubseteq z$ implies $x \ll z$;

(iv) $x \sqsubseteq y \ll z$ implies $x \ll z$;

(v) $x \ll y$ implies $x \sqsubseteq y$;

(vi) $x \ll x$ iff $z \in D : x \sqsubseteq z$ is open;

(vii) if $S \subseteq D$ is directed, then $x \ll \bigsqcup S$ iff $x \ll y$ for some $y \in S$. $\square$

The proofs of these statements can be safely left to the reader.

**2.3 Definition.** A *continuous lattice* is a complete lattice $D$ in which for every $y \in D$ we have:

$$
y = \bigsqcup x \in D : x \ll y.
$$

As an alternate definition we find:

**2.4 Proposition.** A complete lattice $D$ is continuous iff for every $y \in D$ we have:

$$
y = \bigsqcup \sqcap U : y \in U,
$$

where $U$ ranges over the open subsets of $D$.

**Proof:** Suppose $D$ is continuous. If $y \in D$ and $x \ll y$, then let $U = \text{Int}z : x \sqsubseteq z$, an open set. Now $y \in U$ by definition, and $U \subseteq z : x \sqsubseteq z$. Thus,

$$
x \sqsubseteq \sqcap U \sqsubseteq y.
$$

It easily follows by lattice theory that the equation of 2.3 implies that of 2.4.

In the converse direction we have only to note that if $U$ is open and $y \in U$, then $\sqcap U \ll y$. The implication from 2.4 to 2.3 results at once. $\square$

104

What is the idea of this definition? A continuous lattice is more special than a complete lattice: not only are lubs to be limits but every element must be a limit from below. This rather rough remark can be made more precise. In any complete lattice $D$ define the *principal limit* of a net $x : I \to D$ by the formula:

$$
\lim \langle x_i : i \in I \rangle = \bigsqcup \sqcap  x_j : j \ge i  : i \in I .
$$

Then specify that $x$ converges to $y \in D$ iff

$$
y \sqsubseteq \lim \langle x_i : i \in I \rangle.
$$

Having a notion of convergence, we can then say that $U \subseteq D$ is open iff every net converging to an element of $U$ is eventually in $U$. This gives nothing more than what we have called the induced topology above, as is easily checked. But now being in possession of a topology, we can redefine convergence in the usual way. Question: when do the two notions of convergence agree? Answer: if and only if $D$ is a continuous lattice.

For obviously by construction the limit definition of convergence implies the topological. Now if $D$ is a continuous lattice and $x$ converges to $y$ topologically, consider an open $U \subseteq D$ with $y \in U$. For some $i \in I$ we shall have $x_j \in U$ for all $j \ge i$. Therefore

$$
\sqcap U \sqsubseteq \sqcap  x_j : j \ge i  \sqsubseteq \lim \langle x_i : i \in I \rangle.
$$

From the formula of 2.4 it at once follows that $y \sqsubseteq \lim \langle x_i : i \in I \rangle$. Thus, in continuous lattices, we have shown that the two notions of convergence are the same.

Finally, suppose that the two notions coincide for a complete lattice $D$. Define a directed set $I = (U, z) : y, z \in U$, where $z$ ranges over $D$ and $U$ over open subsets of $D$. This set is directed by the relation: $(U, z) \le (V, w)$ iff $U \supseteq V$. Let $x : I \to D$ be given by: $x(U, z) = z$. Then $x$ is a net converging to $y$ topologically. But

$$
\lim \langle x_i : i \in I \rangle = \bigsqcup \sqcap U : y \in U.
$$

In this way we see that the assumption about the two styles of convergence implies that $D$ is a continuous lattice in view of 2.4.

In $T_0$-spaces continuous functions are always monotonic (i.e. $\sqsubseteq$-preserving). For continuous lattices, by virtue of the remarks we have just made about limits, we can define the continuity of $f : D \to D'$ to mean that

$$
f(\lim \langle x_i : i \in I \rangle) \sqsubseteq \lim' \langle f(x_i) : i \in I \rangle
$$

for all nets $x : I \to D$. This is all very fine, but general limits are messy to work with; we shall find it easier to state results in terms of lubs as in 2.5–2.7 below.

Before going any deeper, however, we should clear up another point about topologies. Suppose that $D$ is any $T_0$-space which becomes a complete lattice under its induced partial ordering. Then it is evident from our definitions that every set open in the given topology is also open in the topology induced from the lattice structure. Question: when do the two topologies agree? Answer: a sufficient condition is that the equation:

$$
y = \bigsqcup \sqcap U : y \in U
$$

hold for all $y \in D$, where $U$ ranges over the given open sets. Because in that case if $V$ is open in the lattice sense and $y \in V$, then $\sqcap U \in V$ for some set $U$, open in the given sense, where $y \in U$. But $U \subseteq V$ follows, and so $V$ is a union of given open sets and is itself open in the given topology. Of course this equation implies that $D$ is a continuous lattice by virtue of 2.4. Notice that by the same token the sets of the form $y \in D : x \ll y$ will form a basis for the open sets of a continuous lattice.

105

hold for all $y \in D$, where $U$ ranges over the given open sets. Because in that case if $V$ is open in the lattice sense and $y \in V$, then $\sqcap U \in V$ for some set $U$, open in the given sense, where $y \in U$. But $U \subseteq V$ follows, and so $V$ is a union of given open sets and is itself open in the given topology. Of course this equation implies that $D$ is a continuous lattice by virtue of 2.4. Notice that by the same token the sets of the form $y \in D : x \ll y$ will form a basis for the open sets of a continuous lattice.

**2.5 Proposition.** *If $D$ and $D'$ are complete lattices with their induced topologies, then a function $f : D \to D'$ is continuous iff for all directed subsets $S \subseteq D$:*

$$
f(\bigsqcup S) = \bigsqcup f(x) : x \in S.
$$

**Proof:** If $f : D \to D'$ is continuous, the equation follows from the definition of continuous function and the fact that lubs are limits. Assume then that the equation holds for all directed sets $S$. Let $U' \subseteq D'$ be open in $D'$ and let

$$
U = x \in D : f(x) \in U'.
$$

We must show that $U$ is open in $D$. Note first that if $x \sqsubseteq y$, then $S = x, y$ is directed; hence,

$$
f(x \sqcup y) = f(y) = f(x) \sqcup f(y),
$$

so $f(x) \sqsubseteq f(y)$. Thus $f$ is monotonic and so $U$ satisfies condition (i). That $U$ satisfies condition (ii) follows at once from the above equation. $\square$

**2.6 Proposition.** *With functions from complete lattices to complete lattices, a function of several variables is continuous in the variables jointly iff it is continuous in the variables separately.*

**Proof:** It will be sufficient to discuss functions of two variables. The product $D \times D'$ of two complete lattices is a complete lattice, and it is easy to check that the induced topology is the product topology. Since projection is continuous, joint continuity implies separate continuity. To check the converse suppose that

$$
f : D \times D' \to D''
$$

is a map where the separate continuity holds as follows:

$$
f(\bigsqcup S, y) = \bigsqcup f(x, y) : x \in S
$$

106

and

$$
f(x, \bigsqcup S') = \bigsqcup f(x, y) : y \in S'
$$

where $S \subseteq D$ and $S' \subseteq D'$ are directed and $x \in D$ and $y \in D'$. Let now

$$
S^* \subseteq D \times D'
$$

be directed in the product. The projection of $S^*$ to $D$ and of $S^*$ to $D'$ produces directed subsets $S \subseteq D$ and $S' \subseteq D'$. Note that

$$
\bigsqcup S^* = (\bigsqcup S, \bigsqcup S').
$$

Thus by assumption

$$
f(\bigsqcup S^*) = \bigsqcup f(x, y) : x \in S, y \in S'.
$$

But since $S^*$ is directed, $x \in S$ and $y \in S'$ implies $x \sqsubseteq u$ and $y \sqsubseteq v$ for $(u, v) \in S^*$. Thus by monotonicity of $f$ we can show

$$
f(\bigsqcup S^*) = \bigsqcup f(u, v) : (u, v) \in S^*
$$

and that gives the joint continuity. $\square$

One of the justifications (by euphony at least) of the term *continuous lattice* is the fact that such spaces allow for so many continuous functions. One indication of this is the result:

**2.7 Proposition.** *In a continuous lattice $D$ the finitary lattice operations $\sqcup$ and $\sqcap$ are continuous.*

**Proof:** It is trivial to show that $\sqcup$ is continuous in every complete lattice; this is not so for $\sqcap$. In view of 2.6 we need only show

$$
x \sqcap \bigsqcup S = \bigsqcup x \sqcap y : y \in S
$$

for every directed $S \subseteq D$. In fact it is enough to show

$$
x \sqcap \bigsqcup S \sqsubseteq \bigsqcup x \sqcap y : y \in S
$$

because the opposite inequality is valid in all complete lattices. In view of the fact that $D$ is continuous, it is enough to show that

$$
t \ll x \sqcap \bigsqcup S \text{ implies } t \sqsubseteq \bigsqcup x \sqcap y : y \in S.
$$

So assume $t \ll x \sqcap \bigsqcup S$. Then $t \sqsubseteq x \sqcap \bigsqcup S \sqsubseteq x$. Also $t \ll \bigsqcup S$ because $x \sqcap \bigsqcup S \sqsubseteq \bigsqcup S$. Thus $t \ll y$ for some $y \in S$ since the set

$$
z \in D : t \ll z
$$

is open. But then $t \sqsubseteq y$, and so $t \sqsubseteq x \sqcap y$, and the result follows. $\square$

It is now time to provide some examples of continuous lattices.

107

**2.8 Proposition.** A finite lattice is a continuous lattice. $\square$

**2.9 Proposition.** The Cartesian product of any number of continuous lattices is a continuous lattice with the induced topology agreeing with the product topology.

**2.10 Proposition.** A retract of a continuous lattice is a continuous lattice with the subspace topology agreeing with the induced topology.

It would seem that the continuous lattices are starting to sound suspiciously like the injective spaces. Indeed, if we can prove the following, the circle will be complete.

**2.11 Proposition.** Every continuous lattice is an injective space under its induced topology.

**2.12 Theorem.** The injective spaces are exactly the continuous lattices.

This theorem is an immediate consequence of the preceding results: an injective space is a retract of a power of $\mathbb{O}$. But $\mathbb{O}$ is a finite lattice $(\perp \sqsubseteq \top)$, and so the given space is a continuous lattice under its induced topology. On the other hand a continuous lattice is injective. It remains then to prove 2.9–2.11.

**Proof of 2.9**

Let $D_i$ for $i \in I$ be a system of continuous lattices. The product

$$
D^* = \prod_{i \in I} D_i
$$

is a complete lattice in the usual way and has its induced topology. Suppose $y \in D^*$ and let $i \in I$. Then $y_i \in D_i$. Since $D_i$ is a continuous lattice

$$
y_i = \bigsqcup x \in D_i : x \ll y_i.
$$

For $x \in D_i$, let $[x]^i \in D^*$ be defined by:

$$
[x]^i_j = \begin{cases} x & \text{if } i = j,  \perp & \text{if } i \neq j. \end{cases}
$$

Note that since $D_i$ is continuous we have:

$$
[y_i]^i = \bigsqcup [x]^i : x \ll y_i,
$$

and

$$
y = \bigsqcup [y_i]^i : i \in I.
$$

108

It follows that

$$
y = \bigsqcup \bigcap \{ z : z_i \in U \text{ for all } i \in I,\, y_i \in U \},
$$

where $i$ ranges over $I$ and $U$ over the open subsets of $D_i$, because

$$
[x]^i \sqsubseteq \bigcap  z : z_i \in U , \quad \text{where } U =  u \in D_i : x \ll u .
$$

But the sets $ z : z_i \in U $ are open in the product sense, and so

$$
y = \bigsqcup  \bigcap U : y \in U ,
$$

where $U$ ranges now over the open subsets of the product topology on $D^*$. By the remark following 2.4 we conclude that $D^*$ is continuous with the lattice-induced topology being the product topology. $\square$

**Proof of 2.10**

Let $D'$ be a continuous lattice and let $D \subseteq D'$ be a subspace which is a retract. We have for a suitable $j : D' \to D$,

$$
D =  x \in D' : j(x) = x ,
$$

where of course $j$ is continuous.

*First a note of warning:* though $D$ is a subspace it is not a sublattice; that is, the partial ordering on $D$ is the restriction of that of $D'$, but the lubs of $D$ are not those of $D'$. We shall have to distinguish operations by adding a prime ($'$) for those of $D'$.

Suppose $x, y \in D$. Let $z' = x \sqcup y \in D'$ (join taken in $D'$) and define $z = j(z') \in D$. Now $x \sqsubseteq z'$ and $y \sqsubseteq z'$, and $j$ is monotonic, so $x \sqsubseteq z$ and $y \sqsubseteq z$. Suppose $x \sqsubseteq w$ and $y \sqsubseteq w$ with $w \in D$. Then in $D'$ we have $x \sqcup y \sqsubseteq w$; so $z \sqsubseteq w$ also. Hence we have shown that $z = x \sqcup y$ in $D$.

To show that $D$ has a least element $\bot$ (which may be larger than the $\bot' \in D'$), we need a well-known lemma about monotonic functions: Every monotonic function on a complete lattice into itself has a least fixed point. (Cf. Birkhoff (1970), p. 115.) In our case $j$ is monotonic and

$$
\bot = \sqcap \ x \in D' : j(x) \sqsubseteq x
$$

is the desired element in $D$.

Thus $D$ is at least a semilattice with $\bot$ and $\sqcup$. To show that $D$ is a lattice we need to show that every directed $S \subseteq D$ has a lub in $D$. Now we know ($S' = S$, join taken in the ambient lattice $D'$):

$$
\bigsqcup S' \in D',
$$

and this is a limit of a monotone net. So by 2.1, and the continuity of $j$:

$$
\begin{aligned}
j(\bigsqcup S') &= \bigsqcup  j(x) : x \in S  
&= \bigsqcup S
\end{aligned}
$$

in $D$. In this way we now know that $D$ is a complete lattice. We must

109

still show that $D$ is continuous.

Suppose $y \in D$. In $D'$ we can write:

$$y = \bigsqcup  x \in D' : x \ll y '$$

and this is the limit of a monotone net. Thus

$$j(y) = y = \bigsqcup  j(x) : x \ll y, x \in D' ,$$

where the lub is taken in $D$. Note that the sets

$$U =  z \in D : x \ll z $$

are open in $D$ for each $x \in D'$. Note too that if $z \in U$, then $x \sqsubseteq z$ and so $j(x) \sqsubseteq j(z) = z$. This means that

$$j(x) \sqsubseteq \sqcap U$$

in $D$. We can then write in $D$:

$$y = \bigsqcup \sqcap U : y \in U $$

where $U$ ranges over the open subsets of $D$, and so the lattice is continuous by 2.4. Inasmuch as the open sets $U$ just used were open in the subspace topology, it follows by the remark after 2.4 that the subspace and the lattice-induced topologies coincide. $\square$

++Proof of 2.11++: Let $D$ be a continuous lattice with its induced topology, and let $X \subseteq Y$ be two $T_0$-spaces in the subspace relation. Suppose

$$f : X \to D$$

is continuous. Define

$$\bar{f} : Y \to D$$

by the formula:

$$\bar{f}(y) = \bigsqcup \sqcap f(x) : x \in X \cap U : y \in U ,$$

where $U$ ranges over the open subsets of $Y$. We need to show that $\bar{f}$ extends $f$ and that it is continuous.

First, the continuity: Suppose that $d \in D$ and $d \ll \bar{f}(y)$; that is, $\bar{f}(y)$ belongs to a typical basic open subset of $D$. Since $D$ is continuous, we can also find

$$d \ll d' \ll \bar{f}(y)$$

with $d' \in D$. From the definition of $\bar{f}$ it follows that

$$d' \sqsubseteq \sqcap f(x) : x \in X \cap U $$

for some open $U \subseteq Y$ with $y \in U$. Thus

110

$$d' \sqsubseteq \bar{f}(y')$$

for all $y' \in U$ by virtue of the definition of $\bar{f}$. Since $d \ll d'$, we have also

$$d \ll \bar{f}(y')$$

for all $y' \in U$; in other words, the inverse image of the open subset of $D$ determined by $d$ under $\bar{f}$ is indeed open in $Y$, and $\bar{f}$ is thus continuous.

Next, the extension property: Note that the relationship

$$\bar{f}(x') \sqsubseteq f(x')$$

for all $x' \in X$ comes directly out of the definition of $\bar{f}$. For the converse, suppose $d \ll f(x')$ where $d \in D$. By assumption $f : X \to D$ is continuous, so

$$d \ll f(x'')$$

for all $x'' \in X \cap U$ where $U$ is a suitable open subset of $Y$ with $x' \in U$. In particular we have:

$$d \sqsubseteq \sqcap f(x'') : x'' \in X \cap U ,$$

and so $d \sqsubseteq \bar{f}(x')$. Since $d \ll f(x')$ always implies $d \sqsubseteq \bar{f}(x')$, we see that $f(x') \sqsubseteq \bar{f}(x')$ follows by the continuity of $D$, and the proof is complete. $\square$

The lattice approach to injective spaces gives a completely "internal" characterization of them: in the first place the lattices are complete. Next we can define lattice theoretically:

$$
x \ll y \quad \text{iff} \quad \text{whenever } y \sqsubseteq \bigsqcup Z \text{ and } Z \subseteq D \text{ is directed,}
$$

then $x \sqsubseteq z$ for some $z \in Z$.

Finally we assume that for all $y \in D$:

$$y = \bigsqcup  x \in D : x \ll y .$$

That makes $D$ a continuous lattice with the sets $ y \in D : x \ll y $ as a basis for the topology. Such $T_0$-spaces are injective and every injective space can be obtained in this way with the lattice structure being uniquely determined by the topology. Furthermore, as we have seen, the injective property can be exhibited, as in the proof of 2.11, by an explicit formula for extending functions.

The retract approach to injective spaces should also be considered. The Cartesian powers $\mathbb{O}^I$ are very simple spaces; indeed, as lattices these are just the Boolean algebras of *all subsets* of $I$ (that is, isomorphic thereto). The topology has as a basis the

111

classes of sets containing given finite sets (the *weak topology*, cf. Nerode (1959)). A continuous function

$$j : \mathcal{P}I \to \mathcal{P}I$$

is one of "finite character" so that

$$j(X) = \bigcup  j(F) : F \subseteq X $$

where $X \subseteq I$ and $F$ ranges over *finite sets*. Such a function $j$ is a *retraction* iff it is an *idempotent*:

$$j \circ j = j,$$

which means that the range of $j$ is the set of fixed points of $j$. As we have seen

$$D =  X \in \mathcal{P}I : j(X) = X $$

is a continuous lattice (under $\subseteq$ in this case), and *every* continuous lattice is isomorphic to one obtained in this way. This provides a representation theorem of sorts for continuous lattices, but it does not seem to be of too much help in proving theorems.

The reader should not forget that any space (any *given* number of spaces $X$, $Y$, $\ldots$) can be found as a *subspace* of a continuous lattice $D$. Since $D$ is injective any continuous function $f : X \to Y$ can be extended to a continuous function $\bar{f} : D \to D$. Thus the continuous functions from $D$ into $D$ are a rich totality including *all* the structure of continuous functions on *all* the subspaces. And this remark brings us to the study of function spaces.

**3. FUNCTION SPACES.** We recall the standard definition and introduce our notation for function spaces.

**3.1 Definition.** For $T_0$-spaces $X$ and $Y$ we let $[X \to Y]$ be the *space of all continuous functions* $f : X \to Y$ endowed with the product topology, sometimes called the topology of pointwise convergence. This topology has as a subbase sets of the form:

$$ f : f(x) \in U $$

where $x \in X$ and $U \subseteq Y$ is open.

The pointwise aspect of the topology is immediately apparent in the partial ordering.

**3.2 Proposition.** *The induced partial ordering on $[X \to Y]$ is such that:*

$$f \sqsubseteq g \quad \text{iff} \quad f(x) \sqsubseteq g(x) \text{ for all } x \in X,$$

where $f, g \in [X \to Y]$. $\square$

112

where $f, g \in [X \to Y]$. $\square$

The first question, of course, is what kind of a partial ordering this is.

**3.3 Theorem.** If $D$ and $D'$ are continuous lattices, then so is $[D \to D']$ under the induced partial ordering with the lattice topology agreeing with the product topology.

**Proof:** The argument is "pointwise." Thus, the constant function with value $\bot \in D'$ is obviously continuous and is the $\bot$ of $[D \to D']$ by 3.2. Since by 2.7 the lattice operation $\sqcup$ on $D'$ is continuous, then if $f, g \in [D \to D']$ the composition $f \sqcup g$, defined by

$$(f \sqcup g)(x) = f(x) \sqcup g(x)$$

for all $x \in D$, is also continuous and represents the lub of $f, g$ in $[D \to D']$. (The same arguments apply to $\top$ and $\sqcap$, so $[D \to D']$ is at least a lattice.) To show that $[D \to D']$ is complete it is sufficient now to show that lubs of directed subsets exist. So let $\mathcal{F} \subseteq [D \to D']$ be directed. Define a function from $D$ into $D'$ by the equation:

$$(\bigsqcup \mathcal{F})(x) = \bigsqcup f(x) : f \in \mathcal{F},$$

for all $x \in D$. If we can show that $\bigsqcup \mathcal{F}$ is continuous, then being in $[D \to D']$ it has to be the lub. Consider $U \subseteq D'$, an open subset. Taking the inverse image and remembering that $\mathcal{F}$ is directed, we find:

$$x : (\bigsqcup \mathcal{F})(x) \in U = \bigcup x : f(x) \in U : f \in \mathcal{F}.$$

This is an open set, and so $\bigsqcup \mathcal{F}$ is indeed continuous. (Warning: the infinite $\sqcap \mathcal{F}$ are not in general computed pointwise; however, it is easy to extend the above argument to show that arbitrary $\bigsqcup \mathcal{F}$ are.)

To show that $[D \to D']$ is continuous, we establish first that for $f \in [D \to D']$

$$f = \bigsqcup \overrightarrow{e}[e, e'] : e' \ll f(e),$$

where $e$ ranges over $D$ and $e'$ over $D'$, and where the function $\overrightarrow{e}[e, e']$ is defined by:

$$\overrightarrow{e}[e, e'](x) = \begin{cases} e' & \text{if } e \ll x,  \bot & \text{if not,} \end{cases}$$

for all $x \in D$. Call the function on the right $f'$. Calculate:

113

$$
f'(x) = \bigsqcup \overrightarrow{e}[e, e'](x) : e' \ll f(e)
$$

$$
= \bigsqcup  e' : \exists e \ll x\ [e' \ll f(e)] 
$$

$$
= \bigsqcup  e' : e' \ll f(x)  = f(x).
$$

With the equation for $f$ proved, note next that for all $g \in [D \to D']$, $e' \ll g(e)$ implies $\overrightarrow{e}[e, e'] \sqsubseteq g$ by an easy pointwise argument. If we let $V =  g : e' \ll g(e) $, we see then that $V$ is open in the product topology and that $\overrightarrow{e}[e, e'] \sqsubseteq \sqcap V$. We may then conclude that $f = \bigsqcup  \sqcap V : f \in V $, which proves both that $[D \to D']$ is a continuous lattice and that the two topologies agree by the remark following 2.4. $\square$

The above theorem might possibly be generalized to $[X \to D]$ where $X$ is merely a $T_0$-space, but I was unable to see the argument. In any case we are mostly interested in the continuous lattices. Note as a consequence of our proof:

**3.4 Corollary.** For continuous lattices $D$ and $D'$, the evaluation map:

$$
\mathrm{eval} : [D \to D'] \times D \to D'
$$

is continuous.

**Proof:** Here $\mathrm{eval}(f, x) = f(x)$. With $f$ fixed, this is obviously continuous. With $x$ fixed, we proved the continuity above with our calculation of $\bigsqcup \mathcal{F}$ in view of 2.5. Hence applying 5.3 and 2.6, we conclude that $\mathrm{eval}$ is jointly continuous. $\square$

This result gives only one example of the masses of continuous functions that are available on continuous lattices. As another fundamental example we have:

**3.5 Proposition.** For continuous lattices $D$, $D'$, and $D''$, the map of functional abstraction:

$$
\mathrm{lambda} : [[D \times D'] \to D''] \to [D \to [D' \to D'']]
$$

is continuous.

114

**Proof:** Here lambda is defined by:

$$
\mathrm{lambda}(f)(x)(y) = f(x,y)
$$

where $f \in [[D \times D'] \to D'']$ and $x \in D$ and $y \in D'$. What is particularly interesting here is that by virtue of 3.3 we are making use of $[D \to [D' \to D'']]$ as a continuous lattice. The principle being stated here can be formulated more broadly in this way:

> If an expression $\mathcal{E}(x, y, z, \dots)$ is continuous in all its variables $x, y, z, \dots$ with values in $D'$ as $x$ ranges in $D$, then the expression
>
> $$\lambda x : D . \mathcal{E}(x, y, z, \dots)$$
>
> with values in $[D \to D']$ is continuous in the remaining variables $y, z, \dots$ .

The $\lambda$-notation is a notation for functions, where in the above the variable after the $\lambda$ is the *argument* and the expression after the $.$ is the *value* (as a function of the argument). Thus we could write:

$$
\mathrm{lambda} = \lambda f : [[D \times D'] \to D''] . \lambda x : D . \lambda y : D' . f(x,y),
$$

and, because $f(x,y)$ is continuous in $f$, $x$, and $y$, our conclusion follows. But often it is more readable not to write equations between functions but rather equations between values for definitional purposes.

The proof of the principle is easy. For let the variable $y$, say range over $D''$ and let $S \subseteq D''$ be a directed subset. Then

$$
\begin{aligned}
\lambda x : D . \mathcal{E}(x, \bigsqcup S, z, \dots) &= \lambda x : D . \bigsqcup  \mathcal{E}(x, y, z, \dots) : y \in S  
&= \bigsqcup  \lambda x : D . \mathcal{E}(x, y, z, \dots) : y \in S ,
\end{aligned}
$$

because the lubs of functions are computed pointwise. $\square$

We need not enumerate the many corollaries that follow easily now from this result. We mention, however, that composition $f \circ g$ of functions (on continuous lattices) is continuous in the two function variables, where we write

$$
(f \circ g)(x) = f(g(x)).
$$

What will be useful will be to return at this point to a discussion of the injective properties of continuous lattices. If one continuous lattice is a subspace of another it is of course a retract. This relationship between spaces can be given by a pair of continuous maps

115

$$i : D \to D' \quad \text{and} \quad j : D' \to D,$$

where

$$j \circ i = \text{id}_D = \lambda x : D . x.$$

The composition $i \circ j : D' \to i(D)$ is the retraction onto the subspace corresponding to $D$ under $i$. Now if we have a diagram:

$$
\begin{gathered}
D \xrightarrow[\ j\ ]{i} D' 
f \searrow \qquad \swarrow \tilde{f} = f \circ j 
D''
\end{gathered}
$$

the given continuous $f$ is at once extendable from $D$ to $D'$ by the obvious definition of $\tilde{f}$. This $\tilde{f}$ is not the $\bar{f}$ used in the proof of 2.11, and it will be well to sort out the connections. On one side note that if $f'$ is any function which extends $f$, then we have $f = f' \circ i$. But this implies

$$\tilde{f} = f \circ j = f' \circ i \circ j,$$

which shows that $\tilde{f}$ is a "degraded" version of $f'$. There is one situation where this type of degrading is especially nice.

**3.6 Definition.** A continuous lattice $D$ is said to be a *projection* of a continuous lattice $D'$ iff there are a pair of continuous maps

$$i : D \to D' \quad \text{and} \quad j : D' \to D$$

such that not only

$$j \circ i = \text{id}_D,$$

but also

$$i \circ j \sqsubseteq \text{id}_{D'}.$$

Thus, in case our retraction is a projection, we have $\tilde{f} \sqsubseteq f'$, which means that $\tilde{f}$ is the *minimal* extension of $f \in [D \to D'']$ to a function in $[D' \to D'']$. We will discuss the nature of $\tilde{f}$ in a moment. But before we do we pause to remark that the correspondence $f \rightsquigarrow \tilde{f}$ is *continuous*, and this fact is easily extended.

**3.7 Proposition.** Suppose the two pairs of maps

$$i_n : D_n \to D'_n \quad \text{and} \quad j_n : D'_n \to D_n$$

116

for $n = 0,1$ make $D_n$ a retraction (projection) of $D'_n$. Then $[D_0 \rightarrow D_1]$ is also a retraction (projection) of $[D'_0 \rightarrow D'_1]$ by means of the pair of maps:

$$\vec{i}(f) = i_1 \circ f \circ j_0 \text{ , and}$$

$$\vec{j}(f') = j_1 \circ f' \circ i_0 \text{ ,}$$

where $f \in [D_0 \rightarrow D_1]$ and $f' \in [D'_0 \rightarrow D'_1]$. $\square$

Returning now to $\bar{f}$ we can prove:

**3.8 Proposition.** If $D$ is a continuous lattice and $e : X \rightarrow Y$ a subspace embedding, then for each $f : X \rightarrow D$, the function $\bar{f} : Y \rightarrow D$ given by the formula

$$\bar{f}(y) = \bigsqcup  \sqcap  f(x) : e(x) \in U  : y \in U ,$$

where $U$ ranges over open subsets of $Y$ and $x$ over $X$, is the maximal extension of $f$ to a function in the partially ordered set $[Y \rightarrow D]$.

**Proof:** We are saying that $\bar{f}$ is the maximal solution to the equation

$$f = \bar{f} \circ e.$$

We already know it is a solution, so let $f'$ be any other. We have

$$
\begin{aligned}
f'(y) &= \bigsqcup  \sqcap  f'(z) : z \in U  : y \in U  
&\sqsubseteq \bigsqcup  \sqcap  f'(z) : z \in e(X) \cap U  : y \in U  
&= \bigsqcup  \sqcap  f'(e(x)) : e(x) \in U  : y \in U  
&= \bigsqcup  \sqcap  f(x) : e(x) \in U  : y \in U  
&= \bar{f}(y),
\end{aligned}
$$

which establishes that $f' \sqsubseteq \bar{f}$. $\square$

By the same argument we could show that $\bar{f}$ is the maximal solution of $\bar{f} \circ e \sqsubseteq f$. An interesting question is whether the correspondence $f \rightsquigarrow \bar{f}$ is continuous. I very much doubt it, but at this moment a counterexample escapes me. It is clear that the correspondence is monotonic, for if $f \sqsubseteq g$, then the formula of 3.8 shows that $\bar{f} \sqsubseteq \bar{g}$. This gives us a neat argument for the previous remark: if $g \circ e \sqsubseteq f$, then

$$\overline{g \circ e} \sqsubseteq \bar{f}.$$

But $g \circ e = \overline{g \circ e} \circ e$, so by 3.8, $g \sqsubseteq \overline{g \circ e}$, and $\bar{f}$ is thus maximal.

117

In the case that the range spaces are being extended, the following lemma relating the extensions will be very useful when we consider inverse limits.

**3.9 Lemma.** Consider the diagram:

$$
\begin{gathered}
X \xrightarrow{\quad e\quad} Y 
f \Big\downarrow \qquad\qquad g \searrow \qquad \bar{f} \swarrow \qquad \downarrow \bar{g} 
D \xrightarrow[\ j\ ]{\quad i\quad} D'
\end{gathered}
$$

where the upper row is a subspace embedding and the lower is a projection. If the given functions $f$ and $g$ are extended to $\bar{f}$ and $\bar{g}$ as in 3.8, and if $f = j \circ g$, then $\bar{f} = j \circ \bar{g}$ also.

*Proof:* $\bar{f}$ and $\bar{g}$ are maximal solutions of $f = \bar{f} \circ e$ and $g = \bar{g} \circ e$. Therefore since

$$
f = j \circ g = j \circ \bar{g} \circ e,
$$

we see that

$$
j \circ \bar{g} \sqsubseteq \bar{f}.
$$

Note also that

$$
i \circ \bar{f} \circ e = i \circ f = i \circ j \circ g \sqsubseteq g,
$$

and so by the remark following 3.8, we have

$$
i \circ \bar{f} \sqsubseteq \bar{g}.
$$

Therefore

$$
\bar{f} = j \circ i \circ \bar{f} \sqsubseteq j \circ \bar{g},
$$

which proves the equality. $\square$

Whether this lemma is true for retractions in any form, I do not know. My proof seems to require the stronger projection relationship. I suspect there may be difficulties. In general projections are better behaved than retractions. By the way the word projection seems to be properly used in 3.6, for the projection $j : D \times D' \to D$ of the Cartesian product of two continuous lattices onto the first factor *is* a projection with partial inverse $i : D \to D \times D'$ defined by

$$
i(x) = (x, \bot)
$$

for $x \in D$.

118

**3.10 Proposition.** If the continuous lattice $D$ is a projection of the continuous lattice $D'$ via the pair of maps $i, j$; then for all $S \subseteq D$ and all $x, y \in D$ we have:

(i) $i(\bigsqcup S) = \bigsqcup i(x) : x \in S$,

(ii) $i(x) = i(y)$ implies $x = y$,

(iii) $x \ll y$ implies $i(x) \ll i(y)$.

Conversely, if a map $i : D \to D'$ satisfies (i)–(iii), then there exists a continuous $j : D' \to D$ making $D$ a projection of $D'$, and in fact $j$ is uniquely determined by:

(iv) $j(x') = \bigsqcup x \in D : i(x) \sqsubseteq x'$

for all $x' \in D'$.

**Proof:** Equation (i) holds for directed $S \subseteq D$ because $i$ is continuous. To have it hold for arbitrary $S$ it is only necessary to check it for finite sets, because every lub is the directed lub of finite sublubs. (The last word of that sentence is an unfortunate accident.) Further, to check the equation for finite sets it is enough to check it for the empty set and for two element sets. Thus, $i(\bot) = \bot$, because $j(i(\bot)) = \bot$ and since $\bot \sqsubseteq i(\bot)$,

$$
j(\bot) \sqsubseteq j(i(\bot)) = \bot,
$$

so $j(\bot) = \bot$. Whence $i(\bot) = i(j(\bot)) \sqsubseteq \bot$. Next $i(x \sqcup y) = i(x) \sqcup i(y)$, because first

$$
i(x) \sqcup i(y) \sqsubseteq i(x \sqcup y)
$$

by monotonicity. Then note that

$$
i(x) \sqsubseteq i(x) \sqcup i(y)
$$

and so

$$
x = j(i(x)) \sqsubseteq j(i(x) \sqcup i(y)).
$$

Similarly

$$
y \sqsubseteq j(i(x) \sqcup i(y)),
$$

whence

$$
x \sqcup y \sqsubseteq j(i(x) \sqcup i(y)).
$$

But then

$$
i(x \sqcup y) \sqsubseteq i(j(i(x) \sqcup i(y))) \sqsubseteq i(x) \sqcup i(y),
$$

which completes the argument for equation (i).

119

Condition (ii) is obvious. For (iii) we argue as follows. Assume $x \ll y$. Since $D'$ is continuous we can write:

$$i(y) = \bigsqcup  z' \in D' : z' \ll i(y) ,$$

and conclude by the continuity of $j$ that:

$$y = j(i(y)) = \bigsqcup  j(z') : z' \ll i(y) .$$

But $x \ll y$, so $x \ll j(z')$ for some $z' \ll i(y)$. Now $x \sqsubseteq j(z')$ follows; therefore $i(x) \sqsubseteq i(j(z')) \sqsubseteq z'$. Thus $i(x) \ll i(y)$.

Turning now to the converse, assume of the map $i$ that it satisfies (i)–(iii). Compute:

$$i(j(x')) = \bigsqcup  i(x) : i(x) \sqsubseteq x'  \sqsubseteq x'.$$

This is correct because $i$ is continuous and the set $ x : i(x) \sqsubseteq x' $ is directed in view of condition (i). Thus $i \circ j \sqsubseteq \mathrm{id}_{D'}$. Note that by virtue of (i) and (ii) it is the case that

$$i(x) \sqsubseteq i(y) \text{ implies } x \sqsubseteq y.$$

(The reason is that $x \sqsubseteq y$ is equivalent to $x \sqcup y = y$.) This remark allows us to compute:

$$j(i(y)) = \bigsqcup  x : i(x) \sqsubseteq i(y) $$
$$= \bigsqcup  x : x \sqsubseteq y  = y.$$

Hence, $j \circ i = \mathrm{id}_D$. It remains to show that $j$ is continuous. Suppose $S' \subseteq D'$ is directed. Since $j$ is by definition monotonic, it is sufficient to prove that

$$j(\bigsqcup S') \sqsubseteq \bigsqcup  j(x') : x' \in S' .$$

Now

$$j(\bigsqcup S') = \bigsqcup  x : i(x) \sqsubseteq \bigsqcup S' ,$$

so suppose $i(x) \sqsubseteq \bigsqcup S'$. Let $z \ll x$; whence $i(z) \ll i(x)$. Thus $i(z) \ll x'$ for some $x' \in S'$, and therefore $i(z) \sqsubseteq x'$. We obtain then $z \sqsubseteq j(x')$, which means that

$$z \sqsubseteq \bigsqcup  j(x') : x' \in S' $$

holds for all $z \ll x$. By the continuity of $D$ we conclude

$$x \sqsubseteq \bigsqcup  j(x') : x' \in S' $$

holds for all $x$ with $i(x) \sqsubseteq \bigsqcup S'$. The desired result follows. $\square$

As a corollary of 3.10 we can easily see which *subspaces* of a continuous lattice $D'$ are projections of it. Such a subspace $D \subseteq D'$ must first be closed under $\bigsqcup$. That is, if $S \subseteq D$, then $\bigsqcup S \in D$ for

120

all $S$, where the lub is taken in the sense of $D'$. The identity map on $D$ will then satisfy (i) and (ii). But this is not enough, since we would not know that $D$ is a continuous lattice, nor whether (iii) holds. The following additional condition would be sufficient, if assumed for all $y \in D$:

$$y = \bigsqcup x \in D : x \ll y,$$

where $\ll$ is taken in the sense of $D'$. This implies that

$$y = \bigsqcup \sqcap (D \cap U) : y \in U$$

where $U$ ranges over the open subsets of $D'$ and where the $\sqcap$ is taken in the sense of $D$. This condition makes the subspace topology the same as the lattice topology on $D$ and besides makes $D$ continuous, which is just what we need. (Another way to put it is that whenever $z \ll y$, where $y \in D$ but $z \in D'$, then $z \sqsubseteq x \ll y$, for some $x \in D$.)

It seems a bit troublesome to characterize in a simple way just which maps $j : D' \to D$ are projections. (Other than saying outright that the map $i : D \to D'$ such that for all $x \in D$:

$$i(x) = \sqcap x' \in D' : x \sqsubseteq j(x')$$

is the continuous partial inverse to $j$.) But we can say very easily which continuous maps $j : D' \to D'$ are projections onto *subspaces*; namely, we must have

$$j = j \circ j \sqsubseteq \mathrm{id}.$$

The subspace in question then is:

$$D = x \in D' : j(x) = x.$$

This non-empty subspace is the exact range of $j$ and is closed under $\bigsqcup$. Let $y \in D$. Then if $x' \ll y$ in $D'$, we find $j(x') \sqsubseteq x' \ll y$. Thus since

$$y = \bigsqcup x' \in D' : x' \ll y,$$

we see that

$$y = j(y) = \bigsqcup j(x') : x' \ll y.$$

But each $j(x') \in D$, so $y = \bigsqcup x \in D : x \ll y$, as desired.

The foregoing discussion suggests looking more closely at the space of all projections of a continuous lattice since they are so easily characterized.

121

**3.11 Definition.** Given a continuous lattice $D$, we let the space of projections be denoted by:

$$J_D = j \in [D \to D] : j = j \circ j \sqsubseteq \mathrm{id}.$$

**3.12 Proposition.** For a continuous lattice $D$ the space $J_D$ of projections forms a complete lattice as a $\bigsqcup$-closed subspace of $[D \to D]$.

**Proof:** The constant function $\bot \in J_D$ obviously, so $J_D$ contains $\bigsqcup \emptyset$. Suppose $j, k \in J_D$. We wish to show that $j \sqcup k \in J_D$. Compute:

$$(j \sqcup k)((j \sqcup k)(x)) = j(j(x) \sqcup k(x)) \sqcup k(j(x) \sqcup k(x)).$$

But note:

$$j(x) \sqsubseteq j(j(x)) \sqsubseteq j(j(x) \sqcup k(x)) \sqsubseteq j(x),$$

because $j(x) \sqcup k(x) \sqsubseteq x$. Similarly for $k(x)$. Therefore, we find that $(j \sqcup k) \circ (j \sqcup k) = j \sqcup k \sqsubseteq \mathrm{id}$.

Suppose finally that $S \subseteq J_D$ is directed. We wish to show that $\bigsqcup S \in J_D$. Clearly $\bigsqcup S \sqsubseteq \mathrm{id}$, so compute by continuity of $\circ$:

$$\bigsqcup S \circ \bigsqcup S = \bigsqcup j \circ j : j \in S = \bigsqcup j : j \in S = \bigsqcup S.$$

It follows that $J_D$ is $\bigsqcup$-closed and hence is a complete lattice. $\square$

The significance of the above result becomes clearer if we consider the connection between projections and subspaces. Let us write:

$$D(j) = x \in D : j(x) = x.$$

For $j \in J_D$, each $D(j)$ is a projection of $D$ onto a subspace. We show first that

$$j \sqsubseteq k \quad \text{iff} \quad D(j) \subseteq D(k).$$

Because if $j \sqsubseteq k$, then $j \sqsubseteq j \circ j \sqsubseteq k \circ j \sqsubseteq \mathrm{id} \circ j = j$. Therefore if $j(x) = x$, then $k(x) = k(j(x)) = j(x) = x$, which means that $D(j) \subseteq D(k)$. On the other hand, if $D(j) \subseteq D(k)$, then since $j(D) \subseteq D(j)$, we see that $k \circ j = j$, and so $j \sqsubseteq k \circ \mathrm{id} = k$. Hence $J_D$ is isomorphic to the partially ordered set of subspaces of $D$ that are projections. We thus conclude that these subspaces form a lattice. In fact, it is easy to show that

$$D(j \sqcup k) = x \sqcup y : x \in D(j), y \in D(k).$$

Similarly, if $S$ is a directed set of $J_D$, then $D(\bigsqcup S)$ is the $\bigsqcup$-closure in $D$ of the subset:

$$\bigcup D(j) : j \in S.$$

122

These are not very deep facts, but their proofs were very much facilitated by the introduction of $J_D$ and the utilization of the lattice structure of $[D \to D]$. Along the same line we can define for $j, k \in J_D$ a function $(j \to k) \in [D \to D] \to [D \to D]$ by the equation

$$(j \to k)(f) = k \circ f \circ j.$$

It is very easy to show that $(j \to k) \in J_{[D \to D]}$, that $(j \to k)$ is continuous in $j$ and $k$, and that $[D \to D](j \to k)$ is isomorphic to $[D(j) \to D(k)]$. There are many other interesting operations on projections corresponding to other constructs besides these. And, just as with $(j \to k)$, the operations are continuous. This makes it possible to prove existence theorems about subspaces by using results like the fixed-point theorem for continuous functions. It would be even nicer if $J_D$ turns out to be a continuous lattice itself, but as far as I can tell this is not likely to be the case.

Before we turn to the iterated function-space construction by inverse limits, there are a couple of other connections between spaces and function spaces that are useful to know.

**3.13 Proposition.** Every continuous lattice $D$ is a projection of its function space $[D \to D]$.

**Proof:** Consider the following pair of mappings $\mathrm{con} : D \to [D \to D]$ and $\mathrm{min} : [D \to D] \to D$ where

$$\mathrm{con}(x)(y) = x$$

and

$$\mathrm{min}(f) = f(\bot)$$

for all $x, y \in D$ and $f \in [D \to D]$. They are obviously continuous. The map $\mathrm{con}$ matches every element of $D$ with the corresponding *constant* function in $[D \to D]$. The map $\mathrm{min}$ associates to every function in $[D \to D]$ its *minimum* value in the partial ordering. The proof that this pair forms a projection is trivial. $\square$

The pair $\mathrm{con}$, $\mathrm{min}$ are not the only pair for making $D$ a projection of $[D \to D]$. The following pair of maps were suggested by David Park:

$$\lambda x.\vec{e}[t,x] \quad \text{and} \quad \lambda f. f(t),$$

where $x$ ranges over $D$, and $f$ over $[D \to D]$, and where $t$ is a fixed *isolated* element of $D$ (that is, $t \ll t$ holds). The pair $\mathrm{con}$ and $\mathrm{min}$ will result if we set $t = \bot$. (Note that the expression $\vec{e}[t,x]$, though continuous in $x$, is not continuous—or even monotonic—in the variable $t$.) A lattice may very well possess a large number of isolated

123

elements, whence a large number of projections. And furthermore this is the only way the function $j = \lambda f. f(t)$ can be a projection. For assume the existence of an inverse $i : D \to [D \to D]$ satisfying the proper conditions. Then it would be the case that

$$i(x)(t) = x$$

and

$$i(f(t))(y) \sqsubseteq f(y)$$

for all $x, y \in D$ and all $f \in [D \to D]$. We can prove for all $u \in D$, if $t \not\sqsubseteq u$, then

$$i(x)(u) = \bot$$

by substituting $\vec{e}[v,x]$ for $f$ in the second equation above, where $v$ is chosen so that $v \ll t$ but not $v \ll u$. But then note that

$$i(x)(t) = \bigsqcup i(x)(u) : u \ll t.$$

If not $t \ll t$, then $u \ll t$ implies $t \not\sqsubseteq u$, which leads to absurdity. Hence $t$ must be isolated, and, as we noted earlier, the function $i$ is uniquely determined as being the one we already knew. Aside from these pairs of projections one could obtain others by combinations with automorphisms. I was unable to determine whether there are further pairs of an essentially different nature.

The topic of projections in these spaces is rather interesting since one has in a way more freedom in $T_0$-spaces (particularly in injective spaces) than in ordinary spaces for defining functions. As another example, consider the Cartesian square $D \times D$. Aside from the two obvious projections onto $D$, there is also the “diagonal” system given by the pair:

$$\lambda x.(x,x) \qquad \text{and} \qquad \lambda (x,y). x \sqcap y$$

We shall note in the next section how the choice of an initial projection effects the construction of an inverse limit.

The projections are not the only useful functions in $[D \to D] \to D$. As a final example of what can be done in function spaces we mention the fixed-point operator.

**3.14 Proposition.** *For a continuous lattice $D$ there is a uniquely determined continuous mapping*

$$\mathrm{fix} : [D \to D] \to D$$

*where for all $f \in [D \to D]$ and $x \in D$*

$$f(\mathrm{fix}(f)) = \mathrm{fix}(f)$$

and whenever $f(x) \sqsubseteq x$, then $\mathrm{fix}(f) \sqsubseteq x$.

124

and whenever $f(x) \sqsubseteq x$, then

$$\mathrm{fix}(f) \sqsubseteq x.$$

**Proof:** The proof of the existence of minimal fixed points in complete lattices is well known, as was mentioned in the proof of 2.10.

To establish the continuity, it is sufficient to remark that since all functions $f \in [D \to D]$ are continuous, we have

$$\mathrm{fix}(f) = \bigsqcup_{n=0}^{\infty} f^n(\bot),$$

where $f^n(x) = f(f(\ldots f(x) \ldots))$ ($n$ times). Thus $\mathrm{fix}$ is the point-wise lub of continuous functions on $[D \to D]$ and is thus itself continuous. $\square$

**4. INVERSE LIMITS.** By an *inverse system of spaces* we understand as usual a sequence

$$\langle X_n, j_n \rangle_{n=0}^{\infty}$$

of $T_0$-spaces and continuous maps $j_n : X_{n+1} \to X_n$. The space $X_{\infty}$, called the *inverse limit* of the sequence, is constructed in the familiar way as that subspace of the product space consisting of exactly those infinite sequences

$$x = \langle x_n \rangle_{n=0}^{\infty},$$

where for each $n$ we have $x_n \in X_n$, and

$$j_n(x_{n+1}) = x_n.$$

The space $X_{\infty}$ is given the product topology, and the maps $j_{\infty n} : X_{\infty} \to X_n$ such that

$$j_{\infty n}(x) = x_n$$

are of course continous and satisfy the recursion equation:

$$j_{\infty n} = j_n \circ j_{\infty(n+1)}.$$

Besides this we have the expected extension property for any system of continuous maps

$$f_n : Y \to X_n$$

where for each $n$

$$f_n = j_n \circ f_{n+1}.$$

125

Because, we can define

$$f_{\infty} : Y \to X_{\infty}$$

by the equation

$$f_{\infty}(y) = \langle f_n(y) \rangle_{n=0}^{\infty}$$

for all $y \in Y$; whence

$$f_n = j_{\infty n} \circ f_{\infty}$$

holds. So much for a review of inverse limits. In this paper our interest will center on rather special inverse systems and their limits.

**4.1 Proposition.** Let $\langle D_n, j_n \rangle_{n=0}^{\infty}$ be an inverse system of continuous lattices where each $j_n : D_{n+1} \to D_n$ is a projection. Then the inverse limit space $D_{\infty}$ is also a continuous lattice.

**Proof:** We need only show that $D_{\infty}$ as a $T_0$-space is injective. So suppose $f_{\infty} : X \to D_{\infty}$ is given and $X \subseteq Y$. Define $f_n : X \to D_n$ by $f_n = j_{\infty n} \circ f_{\infty}$. Let $\bar{f}*n : Y \to D_n$ be the maximal extension of $f_n$ according to 3.8. Now we can see the point of Lemma 3.9: by this construction we guarantee that $\bar{f}n = j_n \circ \bar{f}{n+1}$. Hence the required $\bar{f}*{\infty} : Y \to D_{\infty}$ exists. $\square$

I do not know at the time of writing whether this theorem on inverse limits of continuous lattices extends to sequences where, say, the $j_n$ are only retractions. Fortunately, sufficiently many projections exist to make this construction useful. Note that by reference to the product space construction of $D_{\infty}$, its lattice ordering is given simply by the relation:

$$x \sqsubseteq y \quad \text{iff} \quad x_n \sqsubseteq y_n \text{ for all } n.$$

**4.2 Proposition.** Let $\langle D_n, j_n \rangle_{n=0}^{\infty}$ and $D_{\infty}$ be as in 4.1. Then the maps $j_{\infty n} : D_{\infty} \to D_n$ are projections.

**Proof:** The projections $j_n : D_{n+1} \to D_n$, as we know, have their uniquely determined inverses $i_n : D_n \to D_{n+1}$. We can define $i_{n\infty} : D_n \to D_{\infty}$ by the equation:

$$i_{n\infty}(x) = \langle y_m \rangle_{m=0}^{\infty}$$

where

126

$$
y_m = \begin{cases}
j_m(y_{m+1}) & \text{if } m < n, 
x & \text{if } m = n, 
i_m(y_{m-1}) & \text{if } m > n.
\end{cases}
$$

The proof that $i_{n\infty}$ and $j_{\infty n}$ form a projection is now an easy computation. $\square$

One should note also the recursion equation:

$$
i_{n\infty} = i_{(n+1)\infty} \circ i_n.
$$

These maps also make it possible to state this useful equation:

$$
x = \bigsqcup_{n=0}^{\infty} i_{n\infty}(x_n),
$$

where $x \in D_\infty$. It is easy to check that this is a monotone lub, and so we can say each $x \in D_\infty$ is the limit of its projections $x_n$. In fact, from what we know about projections, $x_n$ is the best possible approximation to $x$ in the space $D_n$.

**4.3 Corollary.** Let the spaces be as in 4.1 and 4.2. Let $D'$ be any complete lattice and suppose continuous functions $f_n : D_n \to D'$ are given so that $f_n = f_{n+1} \circ i_n$. Then we can define $f_\infty : D_\infty \to D'$ by the equation:

$$
f_\infty(x) = \bigsqcup_{n=0}^{\infty} f_n(x_n)
$$

for $x \in D_\infty$, and we have $f_n = f_\infty \circ i_{n\infty}$. $\square$

The import of this last result is that within the category of complete lattices, the space $D_\infty$ is not only the inverse limit of the $D_n$, but it is also the *direct* limit. (One system of spaces here uses the $j_n$ as connecting maps, the other the $i_n$.) This is the algebraic result that lies at the heart of our main result about inverse limits of function spaces.

Turning to function spaces, let $D = D_0$ be a given continuous lattice. As we have seen in 3.13, there are many ways of making $D_0$ a projection of $D_1 = [D_0 \to D_0]$. Choose one such given by a pair $i_0, j_0$. Define recursively:

$$
D_{n+1} = [D_n \to D_n]
$$

and introduce the pairs $i_{n+1}, j_{n+1}$ making $D_{n+1}$ a projection of $D_{n+2}$ by the method of 3.7. Specifically we shall have for $x \in D_{n+1}$ and $x' \in D_{n+2}$:

127

$$
i_{n+1}(x) = i_n \circ x \circ j_n,
$$

$$
j_{n+1}(x') = j_n \circ x' \circ i_n.
$$

Since these spaces are more than continuous lattices being function spaces, it is interesting to note that the maps $i_n$ preserve function value as an algebraic operation as follows:

$$
i_n(f(x)) = i_{n+1}(f)(i_n(x)),
$$

where $x \in D_n$ and $f \in D_{n+1}$. Thus in passing to the limit space $D_\infty$ something of functional application must also be preserved. The precise result shows that indeed $D_\infty$ becomes its own function space.

**4.4 Theorem.** *The inverse limit $D_\infty$ of the recursively defined sequence $\langle D_n, j_n \rangle_{n=0}^{\infty}$ of function spaces is not only a continuous lattice, but it is also homeomorphic to its own function space $[D_\infty \to D_\infty]$.*

**Proof:** We can write down directly the pair of maps $i_\infty, j_\infty$ that provide the homeomorphism:

$$
i_\infty(x) = \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ x_{n+1} \circ j_{\infty n}),
$$

$$
j_\infty(f) = \bigsqcup_{n=0}^{\infty} i_{(n+1)\infty}(j_{\infty n} \circ f \circ i_{n\infty}).
$$

Note that these formulae are simply generalizations at the limit for the formulae we used to define $i_n, j_n$ in the first place. Thus it is not surprising that they would provide a projection of $[D_\infty \to D_\infty]$ upon $D_\infty$. Indeed we can compute out $j_\infty(i_\infty(x))$, noting that all the lubs are monotone and that a double monotone limit can always be replaced by a single one in view of the continuity of the operations involved, obtaining

$$
\begin{aligned}
j_\infty(i_\infty(x)) &= \bigsqcup_{n=0}^{\infty} i_{(n+1)\infty}(j_{\infty n} \circ i_{n\infty} \circ x_{n+1} \circ j_{\infty n} \circ i_{n\infty}) 
&= \bigsqcup_{n=0}^{\infty} i_{(n+1)\infty}(x_{n+1}) 
&= x.
\end{aligned}
$$

In the converse order the calculation is only a bit more complicated. The idea is that since all the functions $f$ are continuous and since the elements $x$ are the limits of their approximations, then each $f$ is actually completely determined by its

128

In the converse order the calculation is only a bit more complicated. The idea is that since all the functions $f$ are continuous and since the elements $x$ are the limits of their approximations, then each $f$ is actually completely determined by its sequence of restrictions $j_{\infty n} \circ f \circ i_{n\infty} \in D_{n+1}$. This simple idea can be made more precise with the aid of a lemma about $D_\infty$, which allows us in certain cases to recognize projections from limits.

**4.5 Lemma.** Suppose for each $n$ we have $u_{(n+1)} \in D_{n+1}$ and we let:

$$u = \bigsqcup_{n=0}^{\infty} i_{(n+1)\infty}(u_{(n+1)}).$$

Then if

$$j_{n+1}(u_{(n+2)}) = u_{(n+1)}$$

for each $n$, we can conclude that:

$$j_{\infty(n+1)}(u) = u_{(n+1)}.$$

**Proof:** If the sequence $u_{(n+1)}$ satisfies the recursion, then the limit defining $u$ is monotonic. Therefore by continuity of projection it suffices to prove that

$$j_{\infty(n+1)}(i_{(m+1)\infty}(u_{(m+1)})) = u_{(n+1)}$$

for all $m \geqslant n$. This is obvious for $m = n$, and it can be readily proved by induction for larger $m$ using the various recursion equations. (Properly speaking the induction is done on the quantity $(m - n)$ using both $n$ and $m$ as variables.) $\square$

**Proof of 4.4 concluded:** The lemma applies at once to our calculation, for we find:

$$
\begin{aligned}
i_\infty(j_\infty(f)) &= \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ j_{\infty n} \circ f \circ i_{n\infty} \circ j_{\infty n}) 
&= \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ j_{\infty n}) \circ f \circ \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ j_{\infty n}).
\end{aligned}
$$

Here we have just applied the continuity of $f$ to be able to confine the lub on the right. But now by the remark following 4.2, we note the functional equation:

$$\mathrm{id} = \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ j_{\infty n}),$$

and the proof that $i_\infty$ and $j_\infty$ are inverse to one another is complete. $\square$

We can explain the idea of this proof in other terms using a suggestion made to me by F. W. Lawvere. Consider the category of

129

We can explain the idea of this proof in other terms using a suggestion made to me by F. W. Lawvere. Consider the category of continuous lattices and projections. In that category our $D_\infty$ is, as we have remarked, both a *direct* and an *inverse* limit. Note too that with regard to projections $[D \to D']$ is a *functor*, for we can also define $[j \to j']$ when the maps are projections. In this language our particular inverse system is defined by the recursion:

$$D_{n+1} = [D_n \to D_n] \quad \text{and} \quad j_{n+1} = [j_n \to j_n],$$

where $D_0$ and $j_0$ are given in advance. Now the function space construction is continuous in its two arguments, turning an inverse limit on the right into an inverse limit and a direct limit on the *left* also into an *inverse* limit. A repeated limit can be made into a simple limit, so we can write:

$$
\begin{aligned}
D_\infty &= \varprojlim \langle D_n, j_n \rangle_{n=0}^{\infty} 
&= \varinjlim \langle D_n, i_n \rangle_{n=0}^{\infty}
\end{aligned}
$$

and

$$
\begin{aligned}
[D_\infty \to D_\infty] &= \varprojlim \langle [D_n \to D_n], [j_n \to j_n] \rangle_{n=0}^{\infty} 
&= \varprojlim \langle D_{n+1}, j_{n+1} \rangle_{n=0}^{\infty} 
&= D_\infty \quad \textit{(up to isomorphism).}
\end{aligned}
$$

A full checking of the details involved would not make the argument appreciably simpler over the more "element-by-element" argument I have presented. In fact, the proofs are actually the same. But thinking of the result in terms of properties of functors does seem to isolate very well the essential idea and to show how simple it is.

One must only add here a note of caution: the proper choice of category must be done with care. Thus it seems to me that the use of projections rather than arbitrary continuous maps is necessary.

Inasmuch as I have not checked all details in this form, I hope what I say is correct.

Since we have shown $[D_\infty \to D_\infty]$ to be homeomorphic to $D_\infty$, we can begin to regard them as the same. In particular there ought to be some function space structure to transfer to $D_\infty$. This can be done by defining functional application for any elements $x, y \in D_\infty$ by the equation:

$$x(y) = \bigsqcup_{n=0}^{\infty} i_{n\infty}(x_{n+1}(y_n)).$$

130

Similarly we can define $\lambda$-abstraction on continuous expressions:

$$\lambda x.[\ldots x \ldots] = j_\infty(\lambda x : D_\infty.[\ldots x \ldots]),$$

and in this way $D_\infty$ becomes a model for the $\lambda$-calculus of Church and Curry. The model-theoretic and proof-theoretic aspects of this result will be explained in another paper (Scott (1972)).

Suppose we were to start with the least, non-trivial lattice $0 = \top, \bot$ for $D_0$. Now $D_1 = [0 \to 0]$ has exactly three elements and there are just two ways of defining a projection $j_0 : D_1 \to D_0$. They are illustrated in the figure:

**Left projection**

```
      ⊤  ←── j₀ ──  [⊤,⊤]
      ⊥  ←── j₀ ──  [⊥,⊤]
      ⊥  ←── j₀ ──  [⊥,⊥]
```

**Right projection**

```
      ⊤  ←── j₀ ──  [⊤,⊤]
      ⊤  ←── j₀ ──  [⊥,⊤]
      ⊥  ←── j₀ ──  [⊥,⊥]
```

Hence our construction gives two limit spaces $D_\infty$ and $D'*\infty$. Are they the same? No, they are not. It can be shown, for example, that the $\top$ of $D*\infty$ is *isolated* (that is, $\top \ll \top$), while the same is not true of $D'*\infty$. More interestingly, David Park has proved that the fixed-point operator fix mentioned in 3.14 has algebraic properties in $D*\infty$ quite different from those in $D'*\infty$. By algebraic here, we of course have reference to the functional algebra embodied in the application operation $x(y)$ defined on these limit spaces. Note, by the way, that in view of our isomorphism result we can regard fix (or any other similar continuous function for that matter) as an element of $D*\infty$. This makes the "algebra" of $D_\infty$ quite a rich field for study.

The reader will have surely remarked that by virtue of 1.5, every $T_0$-space $X$ whatsoever can be embedded as a subspace in a $D_\infty$. Besides this all the continuous functions on $X$ (oh, into $D_\infty$, say) can be extended to $D_\infty$; whence they can be regarded as *elements* of $D_\infty$. Thus we have been able to embed not only the topology of $X$ into $D_\infty$ but also all of the continuous function theory over $X$. So far this is only a "logical" construction. For more interesting "mathematical" results we shall have to investigate whether any useful theorems about the usual function spaces $[X \to X]$ can be obtained with the aid of $D_\infty$. This method can easily be employed for real- or complex-valued continuous functions, though it seems more oriented toward pointwise convergence than anything else. Still, there seems to be a chance it might be useful—especially if one wished to consider continuous *operators* on function spaces.

131

The idea of forming the limit space can also be applied to *other* functors besides $[D \to D]$. Thus instead of solving the “equation”

$$D = [D \to D]$$

as we have done with the $D_\infty$ construction, we could also solve:

$$V = T + [V \times V] + [V + V] + [V \to V],$$

for example. Here $T = \bot, 0, 1, \top$ is the four-element lattice with $0$ and $1$ as incomparable elements. By $[V \times V]$ and $[V \to V]$ we understand the usual Cartesian product and function space construction. The $+$ operator, on the other hand works only in the category of lattices with $\top$ as an isolated element. It is defined so as to make:

$$
\begin{array}{ccc}
D + D' & \longleftarrow & D' 
\uparrow & & \uparrow 
D & \longleftarrow & 0
\end{array}
$$

a push-out diagram, where the maps from $0$ are meant to match $\bot$ with $\bot$ and $\top$ with $\top$. The point of requiring $\top$ to be isolated is that both $D$ and $D'$ become projections of $D + D'$. This construction, though not quite a disjoint union, has many properties in common with that operation on spaces. In particular, if we consider the category with projections as maps, the construction

$$\mathbb{F}(D) = T + [D \times D] + [D + D] + [D \to D]$$

is a *functor*. Furthermore, we can project $\mathbb{F}(T)$ onto $T$ in an obvious way, thereby setting things up for an inverse limit construction:

$$V = \varprojlim \langle \mathbb{F}^n(T), j_n \rangle_{n=0}^{\infty}.$$

The resulting continuous lattice satisfies the desired equation up to isomorphism.

The space $V$ constructed in the way just indicated is very rich in subspaces. To see this, consider the space $\mathcal{J}_V$ of proper projections $j$ where $j(\top) = \top$. As in 3.12 this is a complete lattice. Now that $[V \times V]$ and $[V + V]$ and $[V \to V]$ are regarded as *subspaces* of this “universe” $V$ itself, we can easily define *continuous operations*

$$(j \times k)\ ,\ (j + k)\ ,\ \text{and}\ (j \to k)$$

on the projections obtaining again elements of $\mathcal{J}_V$. The projections so obtained correspond to the indicated constructions of subspaces, of course. (Indeed, if we had the time and space, we could show that $\mathcal{J}_V$ becomes a very interesting category). There will be a particular

132

projection $t$ corresponding to $T$, and reason for doing all this is to show that the existence of subspaces of $V$ can now be established by solving equations in $\mathcal{J}_V$. For example, by the fixed-point construction we could find a $j \in \mathcal{J}_V$ such that

$$j = t + (t \times j) + ((j \times j) \to j).$$

The range of $j$ would then be a subspace $W \subseteq V$ such that $W$ solves the equation:

$$W = T + [T \times W] + [[W \times W] \to W].$$

And these are only a few examples: simultaneous equations are possible, and many other operators are waiting for discovery and application.

**REFERENCES.** An announcement of this work and related investigations was first given in Scott (1970). Rather complete references and background material can be found in Scott (1971). A discussion of formal theories is to appear in Scott (1972).

The presentation of the material of the paper changed considerably after the January conference. In the first place remarks by several participants, Ernie Mannes in particular, caused me to rethink several points. Then the opportunity of lecturing at the Project MAC Seminar at MIT during the spring provided the opportunity of trying out some new ideas; these were then codified after lectures at the University of Southern California with the aid of several very helpful discussions on topology with James Dugundji.

The outcome of this development was that I found I could describe the work in purely topological terms in a simple and natural way leaving the lattices to be introduced as a special technique of analysis. This gives the presentation a much less ad hoc appearance, and relates the results to standard point-set topology in a much more understandable way. No doubt the whole idea of using completeness, inverse limits, and continuous functions could be put into a more general, more abstract categorical context, but I am not the man to do it. My interests at present lie in the direction of specific applications, though I can see that there might be some worthwhile directions to pursue.

For example, in understanding the connections of my kind of spaces with other topologies, one should consider the remarks on the topology of lattices in Birkhoff's paper in Abbott (1970). Some

133

older papers such as Strother (1955) or Michael (1951) might also give some leads. It is curious how little there is of interest in the literature on $T_0$-spaces. Concerning function spaces there ought to be some connections with the *limit spaces* of Cook and Fischer (see especially Binz and Keller (1966)) and possibly with the notion of *quasi-topology* of Spanier (1963), but these are rather vague ideas.

In a different direction note that the *algebraic lattices* of Grätzer (1968) are in fact continuous lattices in which isolated points are dense. The continuous lattices may be "higher dimensional" while algebraic lattices are "zero dimensional" - in some suitable sense. Every continuous lattice is a retract of an algebraic lattice.

But does this mean anything? Specific bibliographical references follow:

J. C. Abbott, ed., *Trends in Lattice Theory*, Van Nostrand Reinhold Mathematical Studies, vol. 31 (1970).

P. Alexandroff and H. Hopf, *Topologie I*, Springer-Verlag, (1935).

E. Binz and H. H. Keller, *Funktionenräume in der Kategorie der Limesräume*, Annales Academiae Scientiarum Fennicae, Series A, I. Mathematica, no. 383 (1966), 21 pp.

G. Birkhoff, *Lattice Theory*, American Mathematical Society Colloquium Publications, vol. 25, Third (new) edition (1967).

E. Čech, *Topological Spaces* (revised by Z. Frolík and M. Katětov), Prague (1966).

G. Grätzer, *Universal Algebra*, Van Nostrand, (1968).

J. L. Kelley, *General Topology*, Van Nostrand, (1955).

E. Michael, *Topologies on Spaces of Subsets*, Transactions of the American Mathematical Society, vol. 77 (1951), pp. 152-182.

A. Nerode, *Some Stone Spaces and Recursion Theory*, Duke Mathematical Journal, vol. 26 (1959), pp. 397-406.

134

D. Scott, *Outline of a Mathematical Theory of Computation*, Proceedings of the Fourth Annual Princeton Conference on Information Sciences and Systems (1970), pp. 169-176.

——— , *Lattice Theory, Data Types, and Semantics*, New York University Symposia in Areas of Current Interest in Computer Science (Randall Rustin ed.) (1971) to appear.

——— , *Lattice-theoretic Models for Various Type-free Calculi*, Proceedings of the IVth International Congress for Logic, Methodology, and the Philosophy of Science, Bucharest (1972) to appear.

E. Spanier, *Quasi-topologies*, Duke Mathematical Journal, vol. 30 (1963) pp. 1-14.

W. Strother, *Fixed Points, Fixed Sets, and M-Retracts*, Duke Mathematical Journal, vol. 22 (1955), pp. 551-556.

++Correction++ (Added March, 1972). Robin Milner has pointed out to me that there is an error in the remark in the paragraph immediately preceding Proposition 2.5. I was mistaken in saying that if $D$ is a $T_0$-space which becomes a complete lattice under its induced partial ordering, then every set open in the given topology is also open in the induced topology. There are many counterexamples to this statement. Let $D$ be any complete lattice. There are two extreme $T_0$-topologies which will induce the given partial ordering. The smallest such topology has as a sub-base for its open sets those sets of the form:

$$x \in D : x \not\sqsubseteq y.$$

These sets are easily proved to be open in any $T_0$-topology which induces the partial ordering. At the other extreme consider sets of the form:

$$x \in D : y \sqsubseteq x.$$

135

Such sets will give a base for a $T_0$-topology that is the maximal topology inducing the given partial ordering. Clearly they need not be open in the induced lattice topology; in particular, they may well fail to satisfy conditions (ii) on open sets. To make the remark in question correct, we must thus suppose that the given $T_0$-topology is *contained within* the induced lattice topology. The equation given in the paragraph indicated will then be a sufficient condition for the two topologies to be identical.

The remark was employed in the proof of three different propositions: 2.9, 2.10, and 3.3. In the case of 2.9 one must verify that the product topology is contained within the lattice topology. This need only be done for the basis for the product topology, and for such basic open sets the result needed is obvious. In the case of proposition 2.10 the question concerns a relationship between the topologies of a space and a subspace; the spaces in question are also lattices. Note in passing that a lub in the subspace is generally *larger* in the partial ordering than the corresponding lub relative to the whole space. This puts the inequalities in the wrong direction, and so it is not immediate that a relativized open set for the subspace is open in the lattice topology of the subspace. However, in this case we can appeal to the continuous retraction. Recall that the relativized open sets of the kind that we used in the proof of 2.10 are of the form:

$$U =  z \in D : x < z  \ .$$

Suppose then that $S$ is a directed set, and that using the lub in the sense of $D$ we have

$$\bigsqcup S \in U \ .$$

Referring back to the proof of 2.10 we know that ($S' = S \subseteq D$, but $\bigsqcup S'$ is the join computed in the ambient lattice $D'$)

$$j(\bigsqcup S') = \bigsqcup S \ ,$$

136

which means that

$$x < j(\bigsqcup S') \ .$$

From this it follows that

$$x < j(z), \text{ some } z \in S \ .$$

Now $j(z) = z$ , and we have what we need. This argument suffices only for a special type of open sets; but these open sets form a base for the topology, and so the argument is quite general.

Turning now to the proof of theorem 2.3 we note that the topology on the function space is simply the *relativized* product topology. There is no difficulty with lubs in this case, because, as we showed in the proof of that theorem, all lubs are calculated pointwise. Thus, it is easy to verify now that the sets open in the product topology are also open in the lattice topology.