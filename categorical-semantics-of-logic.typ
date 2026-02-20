#import "common.typ": *

#let CCat = [*CCat*]
#let One = [*1*]
#let dom = [dom]
#let cod = [cod]
#let Mod = [*Mod*]

#show: all.with([Notes on Lawvere Theories], none)

= Cartesian categories
#definition(title: [Cartesian category])[
    A category $cal(C)$ is said to be _cartesian_ if it has all finite products.
]
#definition(title: [Cartesian functor])[
    Given two cartesian categories $cal(C)$ and $cal(D)$, a functor $F : cal(C) -> cal(D)$ is said
    to be _cartesian_ if, for every object $A, B : cal(C)$, the image of the diagram
    #align(center, diagram(spacing: 2cm, $
        A & edge("l", pi_A, ->) A times B edge("r", pi_B, ->) & B
    $))
    by $F$ is a cartesian product of $F(A)$ and $F(B)$.
]

#theorem[
    The category $CCat$ of cartesian categories, with cartesian functors as morphisms, is cartesian 
    closed.
] <thm:ccat-ccc>
#proof[
    First, let's show that it is cartesian.  Because the forgetful functor $CCat -> Cat$ has a left
    adjoint, we know what the finite products must look like, if they exist.  Let's just check that
    they are indeed finite products.
    - The terminal category $One$ is also the terminal cartesian category.  Indeed, for any cartesian
      category $cal(C)$, the unique functor $cal(C) -> One$ is cartesian.
    - Let $cal(A)$ and $cal(B)$ be two cartesian categories.  Let's show that $cal(A) times cal(B)$ is
      cartesian.  Consider $A_1, A_2 : cal(A)$ and $B_1, B_2 : cal(B)$ be objects,  again, thanks to
      the adjunction, we need to check that 
      #align(center, diagram(spacing: 2cm, $
          (A_1, B_1) & (A_1 times A_2, B_1 times B_2) edge("l", (pi_1, pi_1), ->) edge("r", (pi_2, pi_2), ->)
              & (A_2, B_2)
      $))
      is a cartesian product of $(A_1, B_1)$ with $(A_2, B_2)$.  Consider $A' : cal(A)$ and $B' : cal(B)$
      be two objects, and $(f_i, g_i) : (A', B') -> (A_i, B_i)$ for $i : {1, 2}$ be two morphisms.
      Consider the set of morphisms $(chevron f_1, f_2 chevron.r, chevron g_1, g_2 chevron.r)$
      making the following diagram commute
      #align(center, 
          diagram(spacing: (2cm, 3cm), $
              (A_1, B_1) 
                  & (A_1 times A_2, B_1 times B_2) edge("l", (pi_1, pi_1), ->) edge("r", (pi_2, pi_2), ->)
                  & (A_2, B_2) \
                  & (A', B') edge("ul", (f_1, g_1), ->, label-side: #left)
                  edge("u", (chevron f_1, f_2 chevron.r, chevron g_1, g_2 chevron.r), ->, label-pos: #80%)
                  edge("ur", (f_2, g_2), ->, label-side: #right)
          $),
      );
      This is exactly the same as a pair of morphisms $chevron f_1, f_2 chevron.r$ and $chevron g_1,
      g_2 chevron.r$ making the two following diagrams commute
      #grid(columns: (1fr, 1fr), align: center + horizon,
          diagram(spacing: 2cm, $
              A_1 & A_1 times A_2 edge("l", pi_1, ->) edge("r", pi_2, ->) & A_2 \
                  & A' edge("ul", f_1, ->, label-side: #left) edge("u", chevron f_1\, f_2 chevron.r, ->, label-pos: #70%) edge("ur", f_2, ->, label-side: #right)
          $),
          diagram(spacing: 2cm, $
              B_1 & B_1 times B_2 edge("l", pi_1, ->) edge("r", pi_2, ->) & B_2 \
                  & B' edge("ul", g_1, ->, label-side: #left) edge("u", chevron g_1\, g_2 chevron.r, ->, label-pos: #70%) edge("ur", g_2, ->, label-side: #right)
          $)
      );
      both of which exist uniquely.
      
      Besides, we have exhibited a particular choice of product that immediately shows us that $pi_cal(A)
      : cal(A) times cal(B) -> cal(A)$ and $pi_cal(B) : cal(A) times cal(B) -> cal(B)$ are cartesian.

    We now just have to check that $CCat$ is closed.
    
    Consider $cal(A)$ and $cal(B)$ be two cartesian categories, let's consider $cal(B)^cal(A)$ be the
    category of cartesian functors from $cal(A)$ to $cal(B)$, with morphisms natural transformations.
    This category is cartesian: indeed, for two functors $F, G : cal(A) -> cal(B)$, one can form $
        F times G &:& cal(A) &--> cal(B) \
            && X &mapsto.long F(X) times G(X) \
            && f &mapsto.long F(f) times G(f)
    $
    which is clearly a functor, because $F times G = (- times -) compose (F, G) compose Delta_cal(A)$ where 
    $Delta$ is the diagonal in the cartesian category $CCat$.  Furthermore, it is cartesian: indeed, $
        (F times G)(X times Y) &= F(X times Y) times G(X times Y) \
            &tilde.equiv (F(X) times F(Y)) times (G(X) times G(Y)) \
            &tilde.equiv (F(X) times G(X)) times (F(Y) times G(Y)) \
            &= (F times G)(X) times (F times G)(Y)
    $
    where each isomorphism is a canonical isomorphism between finite products.
    
    If we have a cartesian functor $F : cal(B) -> cal(C)$, we can define $
        F^cal(A) &:& cal(B)^cal(A) &--> cal(C)^cal(A) \
            && G &mapsto.long F compose G \
            && alpha &mapsto.long F * alpha
    $
    which is clearly functorial.  It is also immediate that this functor is cartesian.
    
    Let's fix $cal(A) : CCat$ a cartesian category, and let's show that $- times cal(A) tack.l -^cal(A)$. 
    Let $cal(B), cal(C) : CCat$, and consider a cartesian functor $F : cal(B) times cal(A) -> cal(C)$.
    Consider $
        phi(F) &:& cal(B) &--> cal(C)^cal(A) \
            && B &mapsto.long F(B, -) \
            && f &mapsto.long F(f, -)
    $
    It is well-defined.  Let's show that this is a natural in $cal(B)$ and $cal(C)$.  Consider $F : cal(B) -> 
    cal(B)'$ and $G : cal(C) -> cal(C)'$ be two functors.  We have to check that the following diagram 
    commutes
    #align(center, diagram(spacing: 2cm, $
        CCat(cal(B)' times cal(A), cal(C)) edge("r", phi_(cal(B)', cal(C)), ->) edge("d", CCat(F times cal(A), G), ->)
            & CCat(cal(B)', cal(C)^cal(A)) edge("d", CCat(F, G^cal(A)), ->, label-side: #left) \
            CCat(cal(B) times cal(A), cal(C)') edge("r", phi_(cal(B), cal(C)'), ->)
            & CCat(cal(B), cal(C)'^cal(A))
    $))
    Let $H : cal(B)' times cal(A) -> cal(C)'$ be a cartesian functor.  For $B : cal(B)$,
    we have $
        CCat(F, G^cal(A))(phi_(cal(B)',cal(C))(H))(B) &= G compose (phi_(cal(B)', cal(C))(H)(F(B))) \
            &= G compose H(F(B), -) \
            &= G(H(F(B), -)) \
            &= phi_(cal(B), cal(C)')(CCat(F times cal(A), G)(H))(B)
    $
    and same for morphisms.  Furthermore, it is clear that $phi_(cal(B), cal(C))$ is an isomorphism.
]

= Multi-sorted algebraic theories

#definition(title: [Algebraic theory])[
    A _multi-sorted algebraic theory_ is the data of $T = (S, cal(L), dom, cod, A)$, that is, a collection of
    sorts $S$, a language $cal(L)$ composed, for every $n : NN$, of a collection of _symbols of arity $n$ 
    $cal(L)_n$_, with a map $dom_n : cal(L)_n times {1, ..., n} -> S$ and a map $cod_n : cal(L)_n -> S$ giving
    the _signature_ of $cal(L)$, and a set of axioms $A$ that is composed of propositions of the form $u = v$,
    where $u$ and $v$ are open terms.
]

#definition(title: [Model of an algebraic theory])[
    A _model $M$_ of an algebraic theory $T$ is the data of a family of sets $M_s$ for $s : S$, and
    for each $n : NN$, and for each $f : cal(L)_n$, a function $f^M : product_(i = 1)^n M_(dom(f, i)) -> M_cod(f)$
    such that, for each axiom $P : A$, $[|P|]_M$, the interpretation of $P$ in $M$, holds.
]

#definition(title: [Morphism of model])[
    Given $T$ an algebraic theory, and $M, M'$ models of $T$, we define a _morphism between $phi$ between $M$
    and $M'$_ as the data of, for each $s : S$, a map $phi_s : M_s -> M'_s$ such that, for every $n : NN$,
    and every constant $f : cal(L)_n$, the following diagram commutes
    #align(center, diagram(spacing: 2cm, $
        product_(i = 1)^n M_dom(f, i) edge("d", f^M, ->) edge("r", product_(i = 1)^n phi_dom(f, i), ->)
            & product_(i = 1)^n M'_s edge("d", f^M', ->) \
            M_cod(f) edge("r", phi_cod(f), ->) & M'_cod(f)
    $))
]

#definition(title: [Category of models of $T$])[
    Given an algebraic theory $T$, its models, equiped with morphisms of models, form a category $Mod_T$
    of models of $T$.
]

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
    By @thm:ccat-ccc, we have the following series of (natural) isomorphisms $
        Mod_cal(T)_1(Mod_cal(T)_2(cal(C))) &= [cal(T)_1, [cal(T)_2, cal(C)]] \
            &tilde.equiv [cal(T)_1 times cal(T)_2, cal(C)] \
            &tilde.equiv [cal(T)_2 times cal(T)_1, cal(C)] \
            &tilde.equiv [cal(T)_2, [cal(T)_1, cal(C)]] \
            &= Mod_cal(T)_2 (Mod_cal(T)_1(cal(C)))
    $
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
// typst-preview--master-file: "./lawvere-theories.typ"
// End:
