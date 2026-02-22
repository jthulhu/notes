#import "common.typ": *

#let CCat = [*CCat*]
#let One = [*1*]
#let Two = [*2*]
#let dom = [dom]
#let cod = [cod]
#let Mod = [*Mod*]

#show: all.with([Notes on categorical semantics of logic], none)
#show heading.where(level: 1): it => { pagebreak(weak: true); it }

= Categorical theories and their semantics
For this section, consider $cal(F)$ a class of (small) categories.
== $cal(F)$-complete categories

#definition(title: [$cal(F)$-complete category])[
    A $cal(F)$-complete category is a category that has all limits of all shapes $cal(S) : cal(F)$.
]

Let us note $cal(F)Cat$ the category of $cal(F)$-complete categories with morphisms $cal(S)$-continuous
functors for every $cal(S) : cal(F)$.

#example[
    The category of cartesian categories $CCat$ is a category of $cal(F)$-complete categories for $
        cal(F) := {One, 2}
    $
    where $2$ is the discrete category with two elements.
]

#example[
    The category of (finitely) complete categories is a category of $cal(F)$-complete category, by
    taking $cal(F)$ to be the class of all (finite) categories.
]

#remark[
    Multiple different $cal(F)$ can lead to the same category $cal(F)Cat$.  For instance, equalizers
    and finite products are enough to have all finite limits; similarly, having pullbacks and a terminal
    object is enough to have all finite limits.
]

The cornerstone of the theory of $cal(F)$-complete categories is stated as follows.

#theorem[
    $cal(F)Cat$ is cartesian closed.
]
#proof[
    First of all, $cal(F)Cat$ has a terminal object: $One$.  Indeed, $One$ is complete.  Furthermore,
    every functor $cal(C) xarrow(!) One$ is complete.  Let us now consider $cal(C), cal(D) : cal(F)Cat$
    two categories, and let us show that $cal(C) times cal(D)$ is in $cal(F)Cat$.  Let $cal(S) : cal(F)$
    be a shape, and $F : cal(S) -> cal(C) times cal(D)$ a functor.  We can write $F = chevron F_1, F_2 
    chevron.r$.  Let us show that $(lim F_1, lim F_2)$ is a limit of $F$.  This stems from the following
    (natural) identities, for $(X, Y) : cal(C) times cal(D)$: $
        (cal(C) times cal(D))((X, Y), (lim F_1, lim F_2)) &= cal(C)(X, lim F_1) times cal(D)(Y, lim F_2) \
            &tilde.equiv (X => F_1) times (Y => F_2) \
            &tilde.equiv (X, Y) => F_1 times F_2
    $
    By the particular choice of limits in $cal(C) times cal(D)$ that we have exhibited, we can immediately
    deduce that $pi_cal(C) : cal(C) times cal(D) -> cal(C)$ and $pi_cal(D) : cal(C) times cal(D) -> cal(D)$
    are continuous for shapes in $cal(F)$.  It is immediate that $cal(C) times cal(D)$ is a cartesian
    product of $cal(C)$ with $cal(D)$.
    
    Let us finally check that $cal(F)Cat$ is closed.  Consider $cal(C)$ and $cal(D)$ be two categories
    in $cal(F)Cat$, define $cal(D)^cal(C)$ be the category of $cal(F)$-continuous functors, with natural
    transformations as morphisms.  Since limits of shapes in $cal(F)$ exist in $cal(D)$, they exist in
    $cal(D)^cal(C)$.  Since limits are computed pointwise, the same proof that show that $Cat$ is closed
    works to show that $cal(D)^cal(C)$ is an internal hom.
]

== $cal(F)$ theory
#definition(title: [$cal(F)$ theory])[
    A $cal(F)$ theory $cal(T)$ is an $cal(F)$-complete category.
]

A morphism of $cal(F)$ theory is simply a morphism of $cal(F)$-complete category.  In fact, there is
no technical distinction between the category of $cal(F)$ theories and $cal(F)Cat$.  However, in what
follows, we want to see those categories as _theories_, in the sense that they admit a (meta) theory of
models.

== Model of a $cal(F)$ theory
Let $cal(U) : cal(F)Cat$ be a category, called in this context a _universe_, and $cal(T)$ be a $cal(F)$
theory. 

#definition(title: [Model of a theory])[
    A _model M of $cal(T)$ in $cal(U)$_ is a morphism $cal(T) -> cal(U)$, that is, a functor that
    is continuous with respect to all limits of shapes in $cal(F)$.
]

#definition(title: [Morphism of models])[
    Given $M$ and $M'$ be two models of $cal(T)$, a _morphism from $M$ to $M'$_ is a natural 
    transformation $M => M'$.
]

#definition(title: [Category of models])[
    For a given theory $cal(T)$, we define its category of models (in $cal(U)$) $
        Mod_cal(T)(cal(U)) := cal(F)Cat(cal(T), cal(U))
    $
]

#remark[
    We are often primarily interested in models in $Set$ (which belongs to every $cal(F)$Cat).  
    However, being able to change the category in which we interpret are theory will be an
    other important tool to make compute describe theories later on.
]

== Monad on an $cal(F)$ theory
For this section, fix $cal(T)$ a $cal(F)$ theory, and $cal(U)$ be a universe, which has all limits
shaped by $cal(T)$.

#definition(title: [Free algebra monad])[
    Let us note $F_cal(T) : cal(U) -> cal(U)$ the monad on $cal(U)$ derived from the following
    adjunction
    #align(center, diagram(spacing: 2cm, $
        cal(U) edge("r", Delta, ->, shift: #8pt) & Mod_cal(T)(cal(U)) edge("l", lim, ->, shift: #8pt, label-side: #left)
    $,
        node((.4, 0), $bot$),
    ))
    which we call the _free algebra monad over $cal(U)$_.
]

#remark[
    If $cal(U)$ is complete, then in particular it has all limits of shape $cal(T)$, so we can always
    build the free algebra monad over it.
]
#example[
    $Set$ is complete.  Therefore, every theory induces a free algebra monad over the universe $Set$.
    We will see how to recover usual monads on $Set$ with this construction.
]

#proposition[
    The adjunction $Delta tack.l lim$ is monadic.
]
#proof[
    Consider the category $cal(U)^(F_cal(T))$ of algebras of the monad $F_cal(T)$.  There is a functor $
        G : Mod_cal(T)(cal(U)) --> cal(U)^(F_cal(T))
    $
    given by, for any element $M : Mod_cal(T)(cal(U))$, $
        (lim M, lim epsilon_M)
    $
    #margin-note[Finish this proof.]
]

#corollary[
    The category of algebras of the free algebra monad $F_cal(T)$ is isomorphic to the category of models
    of $cal(T)$.
]

= Algebraic theories
For this section, we will consider categories with finite products, that is, $cal(F) = {0, 2}$.

#definition(title: [Multi-sorted Lawvere theory])[
    A $cal(F)$ theory $cal(T)$ is called a _multi-sorted Lawvere theory_.
]
#definition(title: [Category of models of $T$])[
    Given an algebraic theory $T$, its models, equiped with morphisms of models, form a category $Mod_T$
    of models of $T$.
]

#pagebreak(weak: true)
= Horn theories


= Lawvere Theories
#definition(title: [Lawvere theory])[
    A _(generalized) Lawvere theory_ is a cartesian category.
]

#definition(title: [Model of a Lawvere theory])[
    A _model of a lawvere theory $cal(T)$ in a cartesian category $cal(C)$_ is a cartesian functor
    $M : cal(T) -> cal(C)$.
]

#definition(title: [Category of models of a Lawvere theory])[
    Given a Lawvere theory $cal(T)$, we define its _category of models $Mod_cal(T)(cal(C))$ in a cartesian
    category $cal(C)$_ as $
        Mod_cal(T)(cal(C)) = [cal(T), cal(C)]
    $
]

#definition(title: [Morphism of Lawvere theory])[
    Given two Lawvere theories $cal(T)$ and $cal(T)'$, a _morphism of Lawvere theories $cal(T) -> cal(T)'$_
    is a cartesian functor $F : cal(T) -> cal(T)'$.
]

#proposition[
    Given two Lawvere theories $cal(T)$ and $cal(T)'$, and a morphism $F : cal(T) -> cal(T)'$.  Let $cal(C)$
    be a cartesian category.  There exists a cartesian functor $Mod_F (cal(C)) : Mod_cal(T)'(cal(C)) -> 
    Mod_cal(T)(cal(C))$.
]
#proof[
    Let $M : cal(T)' -> cal(C)$, we have $M compose F : cal(T) -> cal(C)$.  Furthermore, given a natural
    transformation $alpha : M_1 -> M_2$, we have $
        alpha * F : M_1 compose F -> M_2 compose F
    $
    which is functorial: $id_M * F = id_(M compose F)$ and $(alpha compose beta) * F = (alpha * F) compose
    (beta * F)$.
    
    Let $M_1, M_2 : cal(T) -> cal(C)$ be two models.  $(M_1 times M_2) compose F = (M_1 compose F) times 
    (M_2 compose F)$ by definition, since limits are computed pointwise.  Similarly, $pi_i * F = pi_i : (M_1 
    compose F) times (M_2 compose F) -> M_i compose F$.
]

#proposition[
    $Mod_-(cal(C)) : CCat^op -> CCat$ est un foncteur contravariant continu.
]
#proof[
    C'est exactement le foncteur $CCat(-, cal(C))$, c'est donc bien un foncteur contravariant, et il est
    bien continu.
]

#example[
    Consider an algebraic theory $T$.  We can build its Lawvere theory $cal(T)$ as follows:
    objects of $cal(T)$ are words of $S$, noted $s_1 times dots.c times s_n$.  A morphism from a
    $product_(i = 1)^n s_i -> product_(i = 1)^m s'_i$ is a tuple $(t_1, ..., t_m)$ where each $t_i$ is a
    term in the context $Gamma := x_1 : s_1, ..., x_n : s_n$ on the language $cal(L)$, quotiented by the
    equivalence relation $t_i ~ t'_i$ if $T tack t_i = t'_i$.
    
    We have an important result: $
        Mod_cal(T)(Set) tilde.equiv Mod_T
    $
]

#theorem[
    Consider $cal(T)_1$ and $cal(T)_2$ two Lawvere theories.  A $cal(T)_1$-model in the category of
    $cal(T)_2$-models is the same thing as a $cal(T)_2$-model in the category of $cal(T)_1$-models.
    In fact, there is a (natural) isomorphism, for any cartesian category $cal(C)$, $
        Mod_cal(T)_1(Mod_cal(T)_2(cal(C))) tilde.equiv Mod_cal(T)_2(Mod_cal(T)_1(cal(C)))
    $
]
#proof[
]

#theorem[
    Two Lawvere theories $cal(T)_1$ and $cal(T)_2$ such that, for any cartesian category $cal(C)$,
    $Mod_cal(T)_1(cal(C)) tilde.equiv Mod_cal(T)_2(cal(C))$ naturally in $cal(C)$, then $cal(T)_1 
    tilde.equiv cal(T)_2$.
]
#proof[
    This stems directly from the Yoneda lemma.
]

// Local Variables:
// typst-preview--master-file: "./categorical-semantics-of-logic.typ"
// End:
