#import "@preview/ctheorems:1.1.3": *
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge
#set text(font: "New Computer Modern")
#set document(title: [Notes on Fibrations], author: "Adrien Mathieu")
#set heading(numbering: "1.")
#show: thmrules.with(qed-symbol: $square$)

#let definition = thmbox("definition", "Definition", inset: (top: .5em))
#let theorem = thmbox("theorem", "Theorem", inset: (top: .5em))
#let lemma = thmbox("lemma", "Lemma", inset: (top: .5em))
#let proof = thmproof("proof", "Proof")
#let Cat = [*Cat*]
#let Fib(C) = $#[*Fib*]_(#C)$
#let Pfct(C) = $#[*Pfct*]_(#C)$
#v(20%)
#align(center, text(25pt)[*Notes on Grothendieck Fibrations*])
#align(center, text(15pt)[Adrien #smallcaps([Mathieu])])
#v(10%)
#outline()
#pagebreak()

#set page(
    footer: align(
        center,
        context counter(page).display("-- 1 --"),
    ) ,
)
#counter(page).update(1)

// Local Variables:
// tp--master-file: "/home/adri/dev/notes/notes.typ"
// End:
