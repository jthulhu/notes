#import "common.typ": *
#show: all.with([Notes on (Co)end Calculus], none)

= Dinaturality and co/ends
#exercise[
    Prove equations (1.5) and (1.6), that is, $
        epsilon.alt_(X, B') compose (u times B') compose (A times f)
            &= epsilon_(X, B) compose (X^f compose u) times B
            & quad & (1.5) \
            epsilon_(X, B') compose (X^B' times f) compose (u times B)
            &= epsilon_(X, B) compose (X^f times B) compose (u times B)
            & & (1.6)
    $
]

// Local Variables:
// typst-preview--master-file: "./coend-calculus.typ"
// End:
